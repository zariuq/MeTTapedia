import Mettapedia.Data.List.OrderedOccurrenceCursor
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# Executable allocation fresh against a finite live occurrence list

The existing occurrence carrier is numbered above every currently live
identity. Payloads and their order are retained, including equal payloads.
This is a current-live allocation contract. It does not promise never to
reuse an identity after deletion; retained historical observers need a wider
avoid set or a monotone supply. The final control exhibits that boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Data.List.FreshOccurrenceAllocation

open OrderedOccurrenceCursor (Occurrence)

variable {Row : Type}

def ceiling : List (Occurrence Row) → Nat
  | [] => 0
  | row :: rest => max (row.identity + 1) (ceiling rest)

def numbered (next : Nat) : List Row → List (Occurrence Row)
  | [] => []
  | value :: rest => ⟨next, value⟩ :: numbered (next + 1) rest

def allocate (live : List (Occurrence Row)) (values : List Row) : List (Occurrence Row) :=
  numbered (ceiling live) values

theorem below_ceiling {live : List (Occurrence Row)} {row : Occurrence Row}
    (member : row ∈ live) : row.identity < ceiling live := by
  induction live with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · simp only [ceiling]
        omega
      · have bounded := ih later
        simp only [ceiling]
        omega

theorem numbered_values (next : Nat) (values : List Row) :
    (numbered next values).map Occurrence.value = values := by
  induction values generalizing next with
  | nil => rfl
  | cons value rest ih => simp [numbered, ih]

theorem numbered_length (next : Nat) (values : List Row) : (numbered next values).length = values.length := by
  have same := congrArg List.length (numbered_values next values)
  simpa only [List.length_map] using same

theorem numbered_bounds (next : Nat) (values : List Row) (row : Occurrence Row)
    (member : row ∈ numbered next values) : next ≤ row.identity ∧ row.identity < next + values.length := by
  induction values generalizing next with
  | nil => cases member
  | cons first rest ih =>
      simp only [numbered, List.mem_cons] at member
      rcases member with rfl | later
      · simp
      · have bounds := ih (next + 1) later
        simp only [List.length_cons]
        omega

theorem numbered_distinct_identities (next : Nat) (values : List Row) :
    ((numbered next values).map Occurrence.identity).Nodup := by
  induction values generalizing next with
  | nil => exact List.nodup_nil
  | cons first rest ih =>
      apply List.nodup_cons.mpr
      refine ⟨?_, ih _⟩
      intro member
      obtain ⟨row, present, same⟩ := List.mem_map.mp member
      change row.identity = next at same
      have bounds := numbered_bounds (next + 1) rest row present
      omega

theorem numbered_nodup (next : Nat) (values : List Row) : (numbered next values).Nodup :=
  List.Nodup.of_map Occurrence.identity (numbered_distinct_identities next values)

theorem allocate_values (live : List (Occurrence Row)) (values : List Row) :
    (allocate live values).map Occurrence.value = values := numbered_values _ _

theorem allocate_nodup (live : List (Occurrence Row)) (values : List Row) :
    (allocate live values).Nodup := numbered_nodup _ _

/-- Freshness holds for identities themselves, not merely for identity/value pairs. -/
theorem fresh_identity (live : List (Occurrence Row)) (values : List Row)
    (made old : Occurrence Row) (newMember : made ∈ allocate live values) (oldMember : old ∈ live) :
    made.identity ≠ old.identity := by
  have lower := (numbered_bounds (ceiling live) values made newMember).1
  have upper := below_ceiling oldMember
  omega

theorem fresh [DecidableEq Row] (live : List (Occurrence Row)) (values : List Row) :
    Disjoint (allocate live values).toFinset live.toFinset := by
  apply Finset.disjoint_left.mpr
  intro row made old
  exact fresh_identity live values row row (List.mem_toFinset.mp made) (List.mem_toFinset.mp old) rfl

namespace Controls

theorem equal_values_keep_two_occurrences :
    allocate ([] : List (Occurrence Nat)) [7, 7] = [⟨0, 7⟩, ⟨1, 7⟩] ∧
      (allocate ([] : List (Occurrence Nat)) [7, 7]).map Occurrence.value = [7, 7] := by
  decide

/-- Current-live freshness does not provide lifetime freshness. A consumer
retaining the old identity cannot silently use this narrower allocation policy. -/
theorem deleted_identity_can_be_reused :
    let first := allocate ([] : List (Occurrence Nat)) [7]
    let afterDeletion : List (Occurrence Nat) := []
    let second := allocate afterDeletion [7]
    first = second ∧ first ≠ [] := by
  decide

end Controls
end Mettapedia.Data.List.FreshOccurrenceAllocation
