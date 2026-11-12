import Mettapedia.Data.List.FreshOccurrenceAllocation

/-!
# Allocation fresh against live and retained occurrence identities

The existing numbered allocator receives the live rows and the finite set of
retained observations. Its empty-retention branch is the original allocator.
Release can therefore permit reuse; no permanent global history is required.
The list is an abstract retention inventory, not a prescribed runtime scan or
data structure. Payload lifetime and finite machine-word supply are separate.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.RetainedOccurrenceAllocation

open OrderedOccurrenceCursor (Occurrence)
open FreshOccurrenceAllocation

variable {Row : Type}

def reserve (live retained : List (Occurrence Row)) (values : List Row) : List (Occurrence Row) :=
  if retained.isEmpty then allocate live values else allocate (live ++ retained) values

theorem reserve_combined (live retained : List (Occurrence Row)) (values : List Row) :
    reserve live retained values = allocate (live ++ retained) values := by
  cases retained <;> simp [reserve]

theorem reserve_values (live retained : List (Occurrence Row)) (values : List Row) :
    (reserve live retained values).map Occurrence.value = values := by
  rw [reserve_combined]
  exact allocate_values _ _

theorem reserve_nodup (live retained : List (Occurrence Row)) (values : List Row) :
    (reserve live retained values).Nodup := by
  rw [reserve_combined]
  exact allocate_nodup _ _

theorem reserve_distinct_identities (live retained : List (Occurrence Row)) (values : List Row) :
    ((reserve live retained values).map Occurrence.identity).Nodup := by
  rw [reserve_combined]
  exact numbered_distinct_identities _ _

theorem fresh_live (live retained : List (Occurrence Row)) (values : List Row)
    (made old : Occurrence Row) (newMember : made ∈ reserve live retained values) (oldMember : old ∈ live) :
    made.identity ≠ old.identity := by
  rw [reserve_combined] at newMember
  exact fresh_identity _ _ made old newMember (List.mem_append_left _ oldMember)

theorem fresh_retained (live retained : List (Occurrence Row)) (values : List Row)
    (made old : Occurrence Row) (newMember : made ∈ reserve live retained values) (oldMember : old ∈ retained) :
    made.identity ≠ old.identity := by
  rw [reserve_combined] at newMember
  exact fresh_identity _ _ made old newMember (List.mem_append_right _ oldMember)

theorem fresh [DecidableEq Row] (live retained : List (Occurrence Row)) (values : List Row) :
    Disjoint (reserve live retained values).toFinset live.toFinset := by
  apply Finset.disjoint_left.mpr
  intro row newMember oldMember
  exact fresh_live live retained values row row (List.mem_toFinset.mp newMember)
    (List.mem_toFinset.mp oldMember) rfl

/-- This profile has no extra allocation input when there are no retained IDs. -/
theorem empty_retention (live : List (Occurrence Row)) (values : List Row) :
    reserve live [] values = allocate live values := rfl

def Avoids (retained current : List (Occurrence Row)) : Prop :=
  ∀ made ∈ current, ∀ old ∈ retained, made.identity ≠ old.identity

theorem reserve_avoids (live retained : List (Occurrence Row)) (values : List Row) :
    Avoids retained (reserve live retained values) := by
  intro made newMember old oldMember
  exact fresh_retained live retained values made old newMember oldMember

theorem avoids_subset (retained first second : List (Occurrence Row))
    (safe : Avoids retained second) (included : ∀ row ∈ first, row ∈ second) : Avoids retained first := by
  intro row member
  exact safe row (included row member)

theorem avoids_append (retained first second : List (Occurrence Row))
    (left : Avoids retained first) (right : Avoids retained second) : Avoids retained (first ++ second) := by
  intro row member
  rcases List.mem_append.mp member with old | new
  · exact left row old
  · exact right row new

namespace Controls

def old : Occurrence Nat := ⟨0, 7⟩

theorem current_live_freshness_can_revive_a_retired_candidate :
    old ∈ allocate [] [7] ∧ old ∉ reserve [] [old] [7] := by decide

theorem retaining_only_live_observers_is_sufficient :
    reserve [] [old] [7] = [⟨1, 7⟩] ∧ reserve [] [] [7] = [old] := by decide

theorem equal_payloads_do_not_merge_new_occurrences :
    reserve [] [old] [7, 7] = [⟨1, 7⟩, ⟨2, 7⟩] := by decide

end Controls

end Mettapedia.Data.List.RetainedOccurrenceAllocation
