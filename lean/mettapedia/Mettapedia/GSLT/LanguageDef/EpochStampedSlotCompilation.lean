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
