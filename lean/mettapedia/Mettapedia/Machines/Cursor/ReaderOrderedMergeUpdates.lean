import Mettapedia.Machines.Cursor.ReaderOrderedMerge

/-!
# Retirement transfers preserve an ordered reader's remainder

A still-unread live occurrence is removed from the live stream and inserted
once into the ordered retirement stream. Occurrences absent from that live
remainder are not inserted: that includes rows already passed. The functional
proof uses actual erase and ordered insertion, not a supplied final equality.

Ordered list insertion is a semantic reference. Its comparison count is
linear in the worst case. A native heap needs its own correctness and height
bound before a logarithmic cost may be claimed.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderOrderedMergeUpdates

open ReaderOrderedMerge
open Mettapedia.TypeTheory

variable {Key : Type} [LinearOrder Key]

def retire (state : State Key) (occurrence : Token Key) : State Key :=
  if occurrence ∈ state.live then
    ⟨state.live.erase occurrence, state.gone.orderedInsert (· ≤ ·) occurrence⟩
  else state

theorem retire_components (state : State Key) (live gone : Finset (Token Key))
    (valid : Components state live gone) (occurrence : Token Key)
    (unread : occurrence ∈ state.live) :
    Components (retire state occurrence) (live.erase occurrence) (insert occurrence gone) := by
  rcases valid with ⟨liveOrdered, goneOrdered, liveUnique, goneUnique, liveSet, goneSet, separate⟩
  have liveMember : occurrence ∈ live := liveSet ▸ List.mem_toFinset.mpr unread
  have absent : occurrence ∉ gone := fun member =>
    Finset.disjoint_left.mp separate liveMember member
  have absentList : occurrence ∉ state.gone := by
    simpa only [← goneSet, List.mem_toFinset] using absent
  unfold retire
  rw [if_pos unread]
  refine ⟨liveOrdered.erase occurrence,
    goneOrdered.orderedInsert occurrence _ , liveUnique.erase occurrence,
    (List.perm_orderedInsert (· ≤ ·) occurrence state.gone).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨absentList, goneUnique⟩), ?_, ?_, ?_⟩
  · ext value
    simp only [List.mem_toFinset, liveUnique.mem_erase_iff, Finset.mem_erase]
    rw [← List.mem_toFinset, liveSet]
  · ext value
    simp [List.mem_orderedInsert, ← goneSet]
  · apply Finset.disjoint_left.mpr
    intro value inLive inGone
    rcases Finset.mem_insert.mp inGone with same | old
    · exact (Finset.mem_erase.mp inLive).1 same
    · exact Finset.disjoint_left.mp separate (Finset.mem_erase.mp inLive).2 old

theorem retire_keeps_meaning (state : State Key) (live gone : Finset (Token Key))
    (valid : Components state live gone) (occurrence : Token Key) :
    meaning (retire state occurrence) = meaning state := by
  by_cases unread : occurrence ∈ state.live
  · have moved := retire_components state live gone valid occurrence unread
    rw [merge_source _ _ _ moved, merge_source _ _ _ valid]
    have present : occurrence ∈ live := valid.2.2.2.2.1 ▸ List.mem_toFinset.mpr unread
    congr 1
    ext value
    by_cases same : value = occurrence
    · subst value; simp [present]
    · simp [same]
  · simp [retire, unread]

/-- Once the occurrence has left the live remainder, repeating retirement
does not enqueue another copy in the removed stream. -/
theorem retire_twice (state : State Key) (occurrence : Token Key)
    (unique : state.live.Nodup) :
    retire (retire state occurrence) occurrence = retire state occurrence := by
  by_cases unread : occurrence ∈ state.live
  · have absent := unique.not_mem_erase (a := occurrence)
    simp [retire, unread, absent]
  · simp [retire, unread]

theorem retirement_preserves_clients {Return : Unit → Unit → Type}
    (state : State Key) (live gone : Finset (Token Key))
    (valid : Components state live gone) (occurrence : Token Key)
    (client : Client (P := Sequence.protocol (Token Key)) (Return := Return))
    (cost : Charge (provider (Key := Key))) (fuel : Nat) (control : client.V () ()) :
    refinement.outcome client
        (advance provider client cost fuel ⟨(), control, retire state occurrence⟩).2 =
      refinement.outcome client
        (advance provider client cost fuel ⟨(), control, state⟩).2 := by
  rw [Hom.advance client refinement cost (fun _ _ => 0),
    Hom.advance client refinement cost (fun _ _ => 0)]
  simp only [Hom.packet, refinement, retire_keeps_meaning state live gone valid occurrence]

def insertionComparisons (occurrence : Token Key) : List (Token Key) → Nat
  | [] => 0
  | first :: later =>
      if occurrence ≤ first then 1 else 1 + insertionComparisons occurrence later

theorem insertion_comparisons_le_length (occurrence : Token Key) (values : List (Token Key)) :
    insertionComparisons occurrence values ≤ values.length := by
  induction values with
  | nil => rfl
  | cons first later ih =>
      unfold insertionComparisons
      split <;> simp only [List.length_cons] <;> omega

theorem insertion_greater_linear (occurrence : Token Key) (values : List (Token Key))
    (last : ∀ value ∈ values, value < occurrence) :
    insertionComparisons occurrence values = values.length := by
  induction values with
  | nil => rfl
  | cons first later ih =>
      have after : ¬ occurrence ≤ first := not_le.mpr (last first (by simp))
      have rest := ih (fun value member => last value (by simp [member]))
      simp [insertionComparisons, after, rest, Nat.add_comm]

end Mettapedia.Machines.Cursor.ReaderOrderedMergeUpdates
