import Mettapedia.Machines.Cursor.ReaderContractionWrites

/-!
# Mixed write/read/copy/compaction schedules
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderContractionWrites.Controls

open StampedSnapshots ReaderContraction

def initial : Runtime Nat := ⟨⟨0, 0, []⟩, [none, none, none]⟩

theorem initial_valid : Valid initial := by
  constructor
  · simp [initial, ReaderContraction.Unique]
  constructor
  · intro cell member
    cases member
  · intro entry member reader same
    simp [initial] at member
    rw [member] at same
    cases same

def events : List (Event Nat) :=
  [.add 7, .add 7, .add 9, .control (.openReader 0), .control (.read 0),
    .remove 1, .add 11, .control (.openReader 1), .control (.read 1), .control (.read 1),
    .control .compact, .remove 0, .add 13, .control (.clone 0 2 true),
    .control (.read 0), .control (.read 2), .control (.read 1), .control (.read 1),
    .control .compact, .control (.read 0), .control (.read 2), .control (.close 1),
    .control (.openReader 1), .control (.read 1), .control (.read 1),
    .control (.read 1), .control (.read 1), .control (.read 1)]

def emitted (replies : List (Reply Nat)) : List (Nat × Nat) :=
  replies.filterMap fun reply => match reply with
    | .value id value => some (id, value)
    | _ => none

theorem joint_expected : emitted (run initial events).2 =
    [(0, 7), (0, 7), (1, 7), (0, 7), (2, 9), (3, 11),
      (2, 9), (1, 7), (2, 9), (3, 11), (4, 13)] := by decide

theorem physical_rows_and_coverage :
    ((run initial events).1.physical.cells.map Cell.id) = [2, 3, 4] ∧
      (run initial events).1.physical.next = 5 := by decide

theorem joint_schedule_earned :
    Valid (run initial events).1 ∧
      observeAll (run initial events).1.physical (run initial events).1.readers =
        (referenceRun initial.physical (observeAll initial.physical initial.readers) events).1 ∧
      (run initial events).2 =
        (referenceRun initial.physical (observeAll initial.physical initial.readers) events).2 :=
  every_joint_schedule initial initial_valid events

def beforeContraction : Runtime Nat := (run initial (events.take 10)).1
def wronglyPacked : Runtime Nat := ⟨compact beforeContraction.physical, beforeContraction.readers⟩
def properlyPacked : Runtime Nat := (apply beforeContraction (.control .compact)).1

theorem physical_drop_without_detach_loses_unread_row :
    (ReaderContraction.apply wronglyPacked (.read 0)).2 = .skip ∧
      (ReaderContraction.apply properlyPacked (.read 0)).2 = .value 1 7 := by decide

theorem no_slot_reuse_after_compaction :
    (run initial events).1.physical.next = 5 ∧
      (add (run initial events).1.physical 17).cells.getLast?.map Cell.id = some 5 := by decide

/-- This explicit implementation detaches each attached clone separately.
Its cost must not be confused with a baseline sharing one owned capture. -/
theorem separate_attached_clone_copies (physical : Physical Nat) (reader : Reader) (copies : Nat) :
    (contract physical (List.replicate copies (some (.attached reader)))).copiedSlots =
      copies * reader.ceiling := by
  rw [(contraction_costs physical _).1]
  induction copies with
  | zero => simp [requiredCopies]
  | succ copies ih => simp [List.replicate_succ, requiredCopies, ih, Nat.add_mul, Nat.add_comm]

theorem already_owned_clone_copies (physical : Physical Nat) (saved : Captured Nat) (copies : Nat) :
    (contract physical (List.replicate copies (some (.owned saved)))).copiedSlots = 0 := by
  rw [(contraction_costs physical _).1]
  induction copies with
  | zero => rfl
  | succ copies ih => simpa [List.replicate_succ, requiredCopies] using ih

def initiallyUnallocated : Runtime Nat := ⟨⟨0, 0, []⟩, []⟩
def growingSchedule : List (Event Nat) :=
  [.add 7, .control (.openReader 20), .control (.read 20),
    .control (.clone 20 50 true), .control .compact, .control (.read 50)]

theorem growing_registry_has_no_fixed_reader_limit :
    (run initiallyUnallocated growingSchedule).1.readers.length = 51 ∧
      emitted (run initiallyUnallocated growingSchedule).2 = [(0, 7), (0, 7)] := by decide

theorem arbitrary_open_grows :
    (apply initiallyUnallocated (.control (.openReader 100))).1.readers[100]? =
      some (some (.attached ⟨0, 0, 0⟩)) := by decide

#print axioms snapshot_add
#print axioms snapshot_remove
#print axioms event_refines
#print axioms every_joint_schedule
#print axioms separate_attached_clone_copies
#print axioms open_allocates_target

end Mettapedia.Machines.Cursor.ReaderContractionWrites.Controls
