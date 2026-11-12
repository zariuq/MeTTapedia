import Mettapedia.Machines.Cursor.ReaderContraction

/-!
# Contraction controls: complete captures, positions, rewind rights and costs
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderContraction.Controls

open StampedSnapshots

def physical : Physical Nat :=
  ⟨4, 3, [⟨0, ⟨7, 1, some 4⟩⟩, ⟨1, ⟨7, 2, none⟩⟩, ⟨2, ⟨9, 3, none⟩⟩]⟩

def advanced : Reader := ⟨3, 3, 1⟩
def saved : Captured Nat := capture (logical physical) ⟨3, 3, 0⟩
def readers : List (Option (Handle Nat)) :=
  [some (.attached advanced), none, some (.owned saved)]

theorem physical_ids_survive :
    ((compact physical).cells.map Cell.id) = [1, 2] := by decide

theorem current_view_survives :
    (current physical).slots = [none, some (1, 7), some (2, 9)] ∧
      current (compact physical) = current physical := by decide

theorem detachment_counts_actual_work :
    (contract physical readers).copiedSlots = 3 ∧
      (contract physical readers).readerVisits = 3 ∧
      (contract physical readers).physicalVisits = 3 := by decide

theorem complete_old_view_and_position_survive :
    (observeAll (contract physical readers).physical (contract physical readers).readers)[0]? =
      some (some ⟨[some (0, 7), some (1, 7), some (2, 9)], 1⟩) := by decide

theorem owned_reader_is_not_copied :
    (detach physical (.owned saved)).2 = 0 ∧
      (detach physical (.owned saved)).1 = .owned saved := by decide

def suffixOnly (reader : Reader) : Captured Nat :=
  ⟨(snapshot (logical physical) reader).drop reader.position, 0⟩

theorem suffix_copy_can_resume :
    (capturedStep (suffixOnly advanced)).1 =
      (capturedStep (capture (logical physical) advanced)).1 := by decide

/-- Duplicate payloads would hide this wrong rewind if occurrence IDs were
discarded. The first original copy has ID0; the suffix starts with ID1. -/
theorem suffix_copy_cannot_rewind_original :
    (capturedStep (capturedRewind (suffixOnly advanced) true)).1 = .value 1 7 ∧
      (capturedStep (capturedRewind (capture (logical physical) advanced) true)).1 = .value 0 7 ∧
      (capturedStep (capturedRewind (suffixOnly advanced) true)).1 ≠
        (capturedStep (capturedRewind (capture (logical physical) advanced) true)).1 := by decide

theorem retaining_old_position_with_suffix_loses_more :
    (capturedStep { suffixOnly advanced with position := advanced.position }).1 = .value 2 9 ∧
      (capturedStep (capture (logical physical) advanced)).1 = .value 1 7 := by decide

theorem full_and_suffix_costs_differ :
    (detach physical (.attached advanced)).2 = 3 ∧
      (suffixOnly advanced).slots.length = 2 := by decide

def initialRuntime : Runtime Nat := ⟨physical, readers⟩

def schedule : List Op :=
  [.read 0, .clone 0 1 true, .compact, .read 1, .read 0,
    .openReader 2, .read 2, .read 2, .read 2,
    .compact, .read 1, .close 0, .read 0]

def emitted (replies : List (Reply Nat)) : List (Nat × Nat) :=
  replies.filterMap fun reply => match reply with
    | .value id value => some (id, value)
    | _ => none

theorem interleaved_schedule_expected :
    emitted (run initialRuntime schedule).2 =
      [(1, 7), (0, 7), (2, 9), (1, 7), (2, 9), (1, 7)] := by decide

theorem schedule_earned_from_refinement :
    observeAll (run initialRuntime schedule).1.physical (run initialRuntime schedule).1.readers =
        (referenceRun (current physical) (observeAll physical readers) schedule).1 ∧
      (run initialRuntime schedule).2 =
        (referenceRun (current physical) (observeAll physical readers) schedule).2 := by
  exact schedule_refines initialRuntime (by simp [initialRuntime, Unique, physical]) schedule

def duplicateId : Physical Nat :=
  ⟨4, 1, [⟨0, ⟨7, 1, some 2⟩⟩, ⟨0, ⟨99, 3, none⟩⟩]⟩

theorem reused_id_breaks_compaction :
    atTime (logical duplicateId) 4 0 = none ∧
      atTime (logical (compact duplicateId)) 4 0 = some (0, 99) := by decide

#print axioms contraction_preserves_readers
#print axioms contraction_costs
#print axioms new_reader_compact
#print axioms schedule_refines

end Mettapedia.Machines.Cursor.ReaderContraction.Controls
