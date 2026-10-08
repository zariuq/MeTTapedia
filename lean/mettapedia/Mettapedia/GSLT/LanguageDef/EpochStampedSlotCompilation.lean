import Mettapedia.GSLT.LanguageDef.ReusableSlotBufferCompilation

/-!
# Certified epoch-stamped finite slot buffers

After finite scratch-slot storage has been allocated once, clearing every slot
before every transaction is still work proportional to the whole slot width.
An implementation may instead attach an epoch to each written slot. Reading a
slot whose stamp differs from the current transaction's fresh epoch returns the
same logical `none` as an explicit clear.

This module isolates the exact admission condition. A finite scan proves that
the selected epoch is absent from the physical buffer. Under that certificate,
stamped execution preserves the complete ordered snapshot produced by a fresh
logical buffer, while performing no width-proportional clearing work. Epoch
wraparound is outside the admitted case until the physical implementation
clears its stamp array and starts a fresh epoch again.
-/

namespace Mettapedia.GSLT.LanguageDef.EpochStampedSlotCompilation

open ReusableSlotBufferCompilation

universe uValue

/-- One physical slot retains its last write epoch and optional payload. -/
abbrev PhysicalSlot (Value : Type uValue) := Nat × Option Value

/-- Fixed-width storage reused across transactions. -/
abbrev StampedBuffer (width : Nat) (Value : Type uValue) :=
  Fin width → PhysicalSlot Value

/-- A stale physical entry is logically absent in the current epoch. -/
def read (epoch : Nat) (buffer : StampedBuffer width Value) :
    Buffer width Value :=
  fun slot => if (buffer slot).1 = epoch then (buffer slot).2 else none

/-- Write one logical slot and stamp it with the current epoch. -/
def writeEntry [DecidableEq (Fin width)]
    (epoch : Nat) (buffer : StampedBuffer width Value)
    (entry : Fin width × Value) : StampedBuffer width Value :=
  fun slot => if slot = entry.1 then (epoch, some entry.2) else buffer slot

def runStamped [DecidableEq (Fin width)]
    (epoch : Nat) :
    StampedBuffer width Value → Transaction width Value →
      StampedBuffer width Value
  | buffer, [] => buffer
  | buffer, entry :: entries =>
      runStamped epoch (writeEntry epoch buffer entry) entries

/-- Reify only the logical current-epoch view. -/
def snapshotStamped (epoch : Nat) (buffer : StampedBuffer width Value) :
    List (Option Value) :=
  snapshot (read epoch buffer)

/-- One stamped write has exactly the same logical effect as one ordinary
write on the current-epoch view. -/
theorem read_writeEntry [DecidableEq (Fin width)]
    (epoch : Nat) (buffer : StampedBuffer width Value)
    (entry : Fin width × Value) :
    read epoch (writeEntry epoch buffer entry) =
      write (read epoch buffer) entry := by
  funext slot
  by_cases same : slot = entry.1
  · subst slot
    simp [read, writeEntry, write]
  · simp [read, writeEntry, write, same]

/-- Stamped execution commutes with the logical current-epoch projection. -/
theorem read_runStamped [DecidableEq (Fin width)]
    (epoch : Nat) (buffer : StampedBuffer width Value)
    (transaction : Transaction width Value) :
    read epoch (runStamped epoch buffer transaction) =
      runFrom (read epoch buffer) transaction := by
  induction transaction generalizing buffer with
  | nil => rfl
  | cons entry entries inductionHypothesis =>
      simp only [runStamped, runFrom]
      rw [inductionHypothesis, read_writeEntry]

/-- The local, decidable certificate required to reuse storage without an
explicit clear. -/
structure AdmittedEpochTransaction (width : Nat) (Value : Type uValue) where
  buffer : StampedBuffer width Value
  epoch : Nat
  transaction : Transaction width Value
  unused : ∀ slot, (buffer slot).1 ≠ epoch

/-- Finite-width recognition of a fresh epoch. -/
def admit?
    (buffer : StampedBuffer width Value) (epoch : Nat)
    (transaction : Transaction width Value) :
    Option (AdmittedEpochTransaction width Value) :=
  if fresh : ∀ slot, (buffer slot).1 ≠ epoch then
    some { buffer, epoch, transaction, unused := fresh }
  else none

/-- A certified unused epoch presents the same logical state as a fully
cleared buffer. -/
theorem read_eq_emptyBuffer
    (admitted : AdmittedEpochTransaction width Value) :
    read admitted.epoch admitted.buffer = emptyBuffer := by
  funext slot
  simp [read, admitted.unused slot, emptyBuffer]

/-- The complete stamped result equals fresh-buffer execution. -/
theorem snapshotStamped_run_eq_fresh [DecidableEq (Fin width)]
    (admitted : AdmittedEpochTransaction width Value) :
    snapshotStamped admitted.epoch
        (runStamped admitted.epoch admitted.buffer admitted.transaction) =
      snapshot (runFresh admitted.transaction) := by
  simp only [snapshotStamped]
  rw [read_runStamped, read_eq_emptyBuffer]
  rfl

/-- Generated artifact retaining the physical buffer and its admitted epoch. -/
structure EpochStampedArtifact (width : Nat) (Value : Type uValue) where
  buffer : StampedBuffer width Value
  epoch : Nat
  transaction : Transaction width Value

def compile (source : AdmittedEpochTransaction width Value) :
    EpochStampedArtifact width Value :=
  { buffer := source.buffer
    epoch := source.epoch
    transaction := source.transaction }

/-- Epoch-stamped clearing elision as a composable certified realization. -/
def epochStampedSlotRealization [DecidableEq (Fin width)] :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedEpochTransaction width Value)
      (EpochStampedArtifact width Value)
      (List (Option Value)) where
  compile := fun _ source => compile source
  observeSource := fun _ source => snapshot (runFresh source.transaction)
  observeArtifact := fun _ artifact =>
    snapshotStamped artifact.epoch
      (runStamped artifact.epoch artifact.buffer artifact.transaction)
  adequate := by
    intro _ source
    exact snapshotStamped_run_eq_fresh source

/-! ## Current-epoch checkpoint transport -/

section CurrentEpochCopy

universe uCopyTarget
variable {width : Nat} {Value : Type uValue} {Target : Type uCopyTarget}

/-- Retain every stamp, transport current payloads, and omit stale payloads.
This logical copy does not inspect payloads outside the captured epoch. Native
allocation, ownership, query-state decoding and cost observations require their
own correspondence. -/
def copyCurrent (epoch : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) : StampedBuffer width Target :=
  fun slot => ((buffer slot).1,
    if (buffer slot).1 = epoch then (buffer slot).2.map mapping else none)

theorem copyCurrent_stamp (epoch : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) (slot : Fin width) :
    (copyCurrent epoch mapping buffer slot).1 = (buffer slot).1 := rfl

/-- All live coordinates, including absent current values, are preserved. -/
theorem read_copyCurrent (epoch : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) :
    read epoch (copyCurrent epoch mapping buffer) = mapValues mapping (read epoch buffer) := by
  funext slot
  by_cases current : (buffer slot).1 = epoch <;> simp [read, copyCurrent, mapValues, current]

theorem copyCurrent_writeEntry (epoch : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) (entry : Fin width × Value) :
    copyCurrent epoch mapping (writeEntry epoch buffer entry) =
      writeEntry epoch (copyCurrent epoch mapping buffer) (entry.1, mapping entry.2) := by
  funext slot
  by_cases same : slot = entry.1 <;> simp [copyCurrent, writeEntry, same]

/-- Subsequent writes in the captured transaction commute with copying. -/
theorem copyCurrent_runStamped (epoch : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) (transaction : Transaction width Value) :
    copyCurrent epoch mapping (runStamped epoch buffer transaction) =
      runStamped epoch (copyCurrent epoch mapping buffer) (mapEntries mapping transaction) := by
  induction transaction generalizing buffer with
  | nil => rfl
  | cons entry entries ih =>
      simp only [runStamped, mapEntries, List.map_cons]
      rw [ih, copyCurrent_writeEntry]
      rfl

theorem snapshotStamped_copyCurrent (epoch : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) :
    snapshotStamped epoch (copyCurrent epoch mapping buffer) =
      (snapshotStamped epoch buffer).map (Option.map mapping) := by
  simp only [snapshotStamped]
  rw [read_copyCurrent, snapshot_mapValues]

/-- Preserving stamps also preserves admission of the next fresh epoch. -/
theorem copyCurrent_unused (epoch next : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) (unused : ∀ slot, (buffer slot).1 ≠ next) :
    ∀ slot, (copyCurrent epoch mapping buffer slot).1 ≠ next := unused

/-- Current logical equality is reflected when payload identities remain
injective. No reflection of arbitrary raw physical-byte observations is claimed. -/
theorem read_copyCurrent_reflects (epoch : Nat) (mapping : Value → Target)
    (faithful : Function.Injective mapping) (first second : StampedBuffer width Value)
    (same : read epoch (copyCurrent epoch mapping first) =
      read epoch (copyCurrent epoch mapping second)) :
    read epoch first = read epoch second := by
  rw [read_copyCurrent, read_copyCurrent] at same
  exact mapValues_injective mapping faithful same

/-- Stale erasure remains exact for future transactions at an admitted fresh
epoch. Reusing a colliding epoch is excluded rather than silently resetting it. -/
theorem snapshotStamped_copyCurrent_future (epoch next : Nat) (mapping : Value → Target)
    (buffer : StampedBuffer width Value) (transaction : Transaction width Value)
    (unused : ∀ slot, (buffer slot).1 ≠ next) :
    snapshotStamped next
      (runStamped next (copyCurrent epoch mapping buffer) (mapEntries mapping transaction)) =
      (snapshot (runFresh transaction)).map (Option.map mapping) := by
  let copied : AdmittedEpochTransaction width Target :=
    ⟨copyCurrent epoch mapping buffer, next, mapEntries mapping transaction,
      copyCurrent_unused epoch next mapping buffer unused⟩
  have exactSnapshot := snapshotStamped_run_eq_fresh copied
  change snapshotStamped next
    (runStamped next (copyCurrent epoch mapping buffer) (mapEntries mapping transaction)) =
      snapshot (runFresh (mapEntries mapping transaction)) at exactSnapshot
  rw [exactSnapshot, runFresh_mapEntries, snapshot_mapValues]

namespace CopyControls

def mixed : StampedBuffer 3 Nat
  | ⟨0, _⟩ => (4, some 11)
  | ⟨1, _⟩ => (3, some 99)
  | ⟨2, _⟩ => (4, some 11)

def mapping (value : Nat) : Nat := 10 + value

theorem current_and_equal_values_preserve_positions :
    snapshotStamped 4 (copyCurrent 4 mapping mixed) = [some 21, none, some 21] := by
  decide

theorem stale_payload_is_not_copied :
    (copyCurrent 4 mapping mixed ⟨1, by omega⟩).1 = 3 ∧
      (copyCurrent 4 mapping mixed ⟨1, by omega⟩).2 = none := by
  decide

theorem admitted_future_transaction :
    snapshotStamped 5
      (runStamped 5 (copyCurrent 4 mapping mixed)
        [(⟨1, by omega⟩, 18), (⟨0, by omega⟩, 12)]) =
      [some 12, some 18, none] := by
  decide

theorem dropping_current_values_changes_observation :
    snapshotStamped 4 (copyCurrent 4 mapping mixed) ≠
      snapshotStamped 4 (fun slot => ((mixed slot).1, none)) := by
  decide

theorem colliding_epoch_is_refused :
    (admit? (copyCurrent 4 mapping mixed) 3 ([] : Transaction 3 Nat)).isSome = false := by
  decide

theorem colliding_epoch_can_reveal_omitted_payload :
    snapshotStamped 3 (copyCurrent 4 mapping mixed) ≠
      (snapshotStamped 3 mixed).map (Option.map mapping) := by
  decide

theorem noninjective_transport_loses_value_identity :
    let first : StampedBuffer 1 Nat := fun _ => (4, some 1)
    let second : StampedBuffer 1 Nat := fun _ => (4, some 2)
    read 4 first ≠ read 4 second ∧
      read 4 (copyCurrent 4 (fun _ => 0) first) =
        read 4 (copyCurrent 4 (fun _ => 0) second) := by
  constructor
  · intro same
    have slot := congrFun same ⟨0, by omega⟩
    simp [read] at slot
  · rfl

end CopyControls

end CurrentEpochCopy

/-! ## Clearing-cost certificate -/

/-- Explicit clearing touches the complete finite slot inventory. -/
def sourceClearTouches (width : Nat) : Nat := width

/-- An admitted fresh epoch starts a transaction without touching any slot. -/
def stampedClearTouches (_width : Nat) : Nat := 0

theorem stampedClearTouches_le_source (width : Nat) :
    stampedClearTouches width ≤ sourceClearTouches width := by
  simp [stampedClearTouches, sourceClearTouches]

theorem stampedClearTouches_lt_source_of_positive
    (width : Nat) (positive : 0 < width) :
    stampedClearTouches width < sourceClearTouches width := by
  simpa [stampedClearTouches, sourceClearTouches] using positive

/-! ## Independent witnesses and rejection boundaries -/

namespace Canaries

private def binderBuffer : StampedBuffer 3 String
  | ⟨0, _⟩ => (4, some "old-x")
  | ⟨1, _⟩ => (3, some "old-y")
  | ⟨2, _⟩ => (4, none)

private def binderTransaction : Transaction 3 String :=
  [(⟨0, by omega⟩, "x"), (⟨2, by omega⟩, "z")]

private def admittedBinder : AdmittedEpochTransaction 3 String where
  buffer := binderBuffer
  epoch := 5
  transaction := binderTransaction
  unused := by decide

/-- A binder environment ignores every stale value without clearing it. -/
example :
    snapshotStamped admittedBinder.epoch
        (runStamped admittedBinder.epoch admittedBinder.buffer
          admittedBinder.transaction) =
      [some "x", none, some "z"] := by
  decide

private def parserBuffer : StampedBuffer 2 Nat
  | ⟨0, _⟩ => (7, some 99)
  | ⟨1, _⟩ => (8, some 88)

private def parserTransaction : Transaction 2 Nat :=
  [(⟨1, by omega⟩, 12)]

/-- Parser/action registers independently exercise the same finite scan. -/
example : (admit? parserBuffer 9 parserTransaction).isSome = true := by
  decide

private def collidingBuffer : StampedBuffer 2 Nat
  | ⟨0, _⟩ => (9, some 99)
  | ⟨1, _⟩ => (8, some 88)

/-- Reusing an epoch still present in storage is rejected. -/
example : (admit? collidingBuffer 9 parserTransaction).isSome = false := by
  decide

/-- Ignoring the fresh-epoch certificate exposes a stale logical value. -/
example :
    snapshotStamped 9 collidingBuffer ≠
      snapshot (emptyBuffer : Buffer 2 Nat) := by
  decide

end Canaries

end Mettapedia.GSLT.LanguageDef.EpochStampedSlotCompilation
