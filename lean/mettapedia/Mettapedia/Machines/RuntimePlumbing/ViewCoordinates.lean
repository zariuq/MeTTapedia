import Mettapedia.Machines.Cursor.ReaderResidualIndex
import Mettapedia.Machines.Cursor.ReaderLoadedSnapshot
import Mathlib.Tactic

/-!
# View-qualified coordinates and residual representation changes

An occurrence is distinct from its term value and from a physical coordinate.
Row coordinates and relation-kept coordinates are different lanes. The same
numeric coordinate in a later view need not identify the same occurrence.

The residual list below is a denotation, not a native cursor representation or
an instruction to materialize candidates. A relocation is verified only on the
unconsumed frontier; the executed prefix is never prepended again.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RuntimePlumbing.ViewCoordinates

variable {Value : Type}

inductive Lane where
  | row (position : Nat)
  | kept (position : Nat)
  deriving DecidableEq, Repr

structure Reference where
  owner : Nat
  view : Nat
  lane : Lane
  deriving DecidableEq, Repr

structure Occurrence where
  owner : Nat
  serial : Nat
  deriving DecidableEq, Repr

structure Layout (Value : Type) where
  owner : Nat
  view : Nat
  row : Nat → Option (Occurrence × Value)
  kept : Nat → Option (Occurrence × Value)

def decode (layout : Layout Value) (reference : Reference) : Option (Occurrence × Value) :=
  if reference.owner = layout.owner ∧ reference.view = layout.view then
    match reference.lane with
    | .row position => layout.row position
    | .kept position => layout.kept position
  else none

def remaining (layout : Layout Value) (frontier : List Reference) : List (Occurrence × Value) :=
  frontier.filterMap (decode layout)

def relocate (move : Reference → Reference) (frontier : List Reference) : List Reference :=
  frontier.map move

/-- The local law includes identity and payload, not just equal-looking terms. -/
theorem relocate_preserves_residual (before after : Layout Value)
    (move : Reference → Reference) (frontier : List Reference)
    (same : ∀ reference ∈ frontier, decode after (move reference) = decode before reference) :
    remaining after (relocate move frontier) = remaining before frontier := by
  unfold remaining relocate
  rw [List.filterMap_map]
  exact List.filterMap_congr same

theorem wrong_view_refuses (layout : Layout Value) (reference : Reference)
    (different : reference.view ≠ layout.view) : decode layout reference = none := by
  simp [decode, different]

theorem wrong_owner_refuses (layout : Layout Value) (reference : Reference)
    (different : reference.owner ≠ layout.owner) : decode layout reference = none := by
  simp [decode, different]

/-- Physical residency does not change the logical residual or index transfer.
Only the requested slot must load before the next stamped step can proceed. -/
theorem loaded_step_and_index_transfer {Key : Type} [DecidableEq Key]
    (store : Cursor.StampedSnapshots.Store (List Key))
    (old fresh : Cursor.StampedSnapshotsIndex.Index Key)
    (oldValid : Cursor.StampedSnapshotsIndex.Valid store old)
    (freshValid : Cursor.StampedSnapshotsIndex.Valid store fresh)
    (reader : Cursor.StampedSnapshots.Reader)
    (oldCovered : reader.ceiling ≤ old.coverage) (freshCovered : reader.ceiling ≤ fresh.coverage)
    (cache : Cursor.ReaderLoadedSnapshot.Cache (List Key)) (column : Nat) (key : Key) :
    Cursor.ReaderLoadedSnapshot.step
        (Cursor.ReaderLoadedSnapshot.load store cache reader.position) reader =
      .ready (Cursor.StampedSnapshots.step store reader).1
        (Cursor.StampedSnapshots.step store reader).2 ∧
    Cursor.ReaderResidualIndex.chainResidual store old reader column key =
      Cursor.ReaderResidualIndex.bitResidual store fresh reader column key :=
  ⟨Cursor.ReaderLoadedSnapshot.step_after_load store cache reader,
    Cursor.ReaderResidualIndex.transfer_preserves_residual store old fresh oldValid freshValid
      reader oldCovered freshCovered column key⟩

namespace Controls

def old : Layout Nat :=
  ⟨1, 5, fun position =>
    if position = 0 then some (⟨1, 7⟩, 9)
    else if position = 3 then some (⟨1, 8⟩, 9) else none,
    fun position => if position = 0 then some (⟨1, 9⟩, 11) else none⟩

def compacted : Layout Nat :=
  ⟨1, 5, fun position => if position = 0 then some (⟨1, 8⟩, 9) else none, old.kept⟩

def move (reference : Reference) : Reference :=
  match reference.lane with
  | .row 3 => { reference with lane := .row 0 }
  | _ => reference

def frontier : List Reference := [⟨1, 5, .row 3⟩, ⟨1, 5, .kept 0⟩]

theorem lane_tags_disambiguate_the_same_number :
    decode old ⟨1, 5, .row 0⟩ = some (⟨1, 7⟩, 9) ∧
      decode old ⟨1, 5, .kept 0⟩ = some (⟨1, 9⟩, 11) := by decide

theorem compacted_frontier_preserves_occurrences_not_just_values :
    remaining compacted (relocate move frontier) = remaining old frontier ∧
      remaining old frontier = [(⟨1, 8⟩, 9), (⟨1, 9⟩, 11)] := by
  constructor
  · apply relocate_preserves_residual
    intro reference member
    simp only [frontier, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  · decide

theorem keeping_raw_coordinates_through_compaction_loses_a_row :
    remaining compacted frontier ≠ remaining old frontier := by decide

theorem resetting_to_the_entry_replays_an_equal_payload_occurrence :
    remaining old (⟨1, 5, .row 0⟩ :: frontier) ≠ remaining old frontier ∧
      (remaining old (⟨1, 5, .row 0⟩ :: frontier)).map Prod.snd = [9, 9, 11] := by decide

def newer : Layout Nat :=
  ⟨1, 6, fun position => if position = 3 then some (⟨1, 20⟩, 100) else none, fun _ => none⟩

theorem reopening_at_the_same_coordinate_adopts_new_data :
    decode newer ⟨1, 5, .row 3⟩ = none ∧
      decode newer ⟨1, 6, .row 3⟩ = some (⟨1, 20⟩, 100) := by decide

def slotStore : Cursor.StampedSnapshots.Store Nat :=
  Cursor.StampedSnapshots.add Cursor.StampedSnapshots.empty 42

def slotReader := Cursor.StampedSnapshots.start slotStore

theorem missing_residency_is_pending_without_advancement :
    Cursor.ReaderLoadedSnapshot.step (Cursor.ReaderLoadedSnapshot.unloaded :
      Cursor.ReaderLoadedSnapshot.Cache Nat) slotReader = .pending slotReader := by decide

theorem loading_only_the_next_slot_releases_the_next_answer :
    Cursor.ReaderLoadedSnapshot.step
      (Cursor.ReaderLoadedSnapshot.load slotStore Cursor.ReaderLoadedSnapshot.unloaded 0)
      slotReader = .ready (.value 0 42) ⟨1, 1, 1⟩ := by decide

theorem authoritative_absence_and_exhaustion_remain_distinct :
    Cursor.ReaderLoadedSnapshot.step
      (Cursor.ReaderLoadedSnapshot.load (Cursor.StampedSnapshots.remove slotStore 0)
        Cursor.ReaderLoadedSnapshot.unloaded 0)
      (Cursor.StampedSnapshots.start (Cursor.StampedSnapshots.remove slotStore 0)) =
        .ready .skip ⟨2, 1, 1⟩ ∧
    Cursor.ReaderLoadedSnapshot.step (Cursor.ReaderLoadedSnapshot.unloaded :
      Cursor.ReaderLoadedSnapshot.Cache Nat) ⟨0, 0, 0⟩ = .ready .exhausted ⟨0, 0, 0⟩ := by decide

end Controls

end Mettapedia.Machines.RuntimePlumbing.ViewCoordinates
