import Mettapedia.Machines.RelationColumnOwnership

/-!
# Zero-crossing retain and release receipts

An external reference counter observes callback occurrences, not just a set
of owned IDs. These executable receipt lists follow the same per-column
updates as the relation bookkeeping. Their membership and no-duplicate laws
establish exactly one callback at each required zero crossing.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationHoldReceipts

open RelationColumnOwnership
variable {Id : Type} [DecidableEq Id]

def acquired : Counters Id → List Id → List Id
  | _, [] => []
  | state, id :: rest =>
      (if state.uses id = 0 then [id] else []) ++ acquired (hold state id) rest

def released : Counters Id → List Id → List Id
  | _, [] => []
  | state, id :: rest =>
      (if state.uses id = 1 then [id] else []) ++ released (unhold state id) rest

theorem acquired_mem (state : Counters Id) (row : List Id) (observed : Id) :
    observed ∈ acquired state row ↔ observed ∈ row ∧ state.uses observed = 0 := by
  induction row generalizing state with
  | nil => simp [acquired]
  | cons id rest ih =>
      by_cases same : observed = id
      · subst observed
        by_cases zero : state.uses id = 0 <;> simp [acquired, ih, hold, zero]
      · by_cases zero : state.uses id = 0 <;> simp [acquired, ih, hold, zero, same]

theorem acquired_nodup (state : Counters Id) (row : List Id) : (acquired state row).Nodup := by
  induction row generalizing state with
  | nil => simp [acquired]
  | cons id rest ih =>
      by_cases zero : state.uses id = 0
      · simp [acquired, zero, ih, acquired_mem, hold]
      · simpa [acquired, zero] using ih (hold state id)

theorem acquired_sublist (state : Counters Id) (row : List Id) : (acquired state row).Sublist row := by
  induction row generalizing state with
  | nil => exact .refl _
  | cons id rest ih =>
      by_cases zero : state.uses id = 0
      · simpa [acquired, zero] using (ih (hold state id)).cons_cons id
      · simpa [acquired, zero] using (ih (hold state id)).cons id

theorem released_sublist (state : Counters Id) (row : List Id) : (released state row).Sublist row := by
  induction row generalizing state with
  | nil => exact .refl _
  | cons id rest ih =>
      by_cases last : state.uses id = 1
      · simpa [released, last] using (ih (unhold state id)).cons_cons id
      · simpa [released, last] using (ih (unhold state id)).cons id

private theorem remaining_budget (state : Counters Id) (id : Id) (rest : List Id)
    (enough : ∀ observed, (id :: rest).count observed ≤ state.uses observed) :
    ∀ observed, rest.count observed ≤ (unhold state id).uses observed := by
  intro observed
  have bound := enough observed
  by_cases same : observed = id
  · subst observed
    simp only [List.count_cons_self] at bound
    simp only [unhold, Function.update_self]
    omega
  · simpa [unhold, same, Ne.symm same] using bound

theorem released_mem (state : Counters Id) (row : List Id) (observed : Id)
    (enough : ∀ id, row.count id ≤ state.uses id) :
    observed ∈ released state row ↔ observed ∈ row ∧ state.uses observed = row.count observed := by
  induction row generalizing state with
  | nil => simp [released]
  | cons id rest ih =>
      have tail := ih (unhold state id) (remaining_budget state id rest enough)
      rw [released, List.mem_append, tail]
      by_cases same : observed = id
      · subst observed
        have bound := enough id
        simp only [List.count_cons_self] at bound
        have membership : id ∈ rest ↔ 0 < rest.count id := List.count_pos_iff.symm
        by_cases last : state.uses id = 1
        · have zero : rest.count id = 0 := by omega
          have absent := List.count_eq_zero.mp zero
          simp [last, unhold, zero, absent]
        · simp [last, unhold]
          rw [membership]
          omega
      · by_cases last : state.uses id = 1 <;>
          simp [last, unhold, same, Ne.symm same]

theorem released_nodup (state : Counters Id) (row : List Id)
    (enough : ∀ id, row.count id ≤ state.uses id) : (released state row).Nodup := by
  induction row generalizing state with
  | nil => simp [released]
  | cons id rest ih =>
      have budget := remaining_budget state id rest enough
      have tail := ih (unhold state id) budget
      by_cases last : state.uses id = 1
      · have bound := enough id
        have absent : id ∉ rest := by
          simp only [List.count_cons_self] at bound
          have zero : rest.count id = 0 := by omega
          exact List.count_eq_zero.mp zero
        rw [released]
        simp only [last, ↓reduceIte, List.singleton_append, List.nodup_cons]
        exact ⟨fun member => absent ((released_mem _ _ _ budget).mp member).1, tail⟩
      · simpa [released, last] using tail

theorem acquire_iff_new_owner (state : Counters Id) (valid : state.Valid) (row : List Id) (id : Id) :
    id ∈ acquired state row ↔ id ∉ state.owned ∧ id ∈ (holdColumns state row).owned := by
  rw [acquired_mem, valid id, (holdColumns_valid state valid row) id, holdColumns_uses]
  have membership : id ∈ row ↔ 0 < row.count id := List.count_pos_iff.symm
  rw [membership]
  omega

theorem release_iff_lost_owner (state : Counters Id) (valid : state.Valid) (row : List Id) (id : Id)
    (enough : ∀ observed, row.count observed ≤ state.uses observed) :
    id ∈ released state row ↔ id ∈ state.owned ∧ id ∉ (unholdColumns state row).owned := by
  rw [released_mem state row id enough, valid id, (unholdColumns_valid state valid row) id, unholdColumns_uses]
  have membership : id ∈ row ↔ 0 < row.count id := List.count_pos_iff.symm
  rw [membership]
  have bound := enough id
  omega

namespace Controls

def counters : Counters Nat := ⟨fun _ => 0, ∅⟩

theorem repeated_columns_emit_one_retain : acquired counters [7, 7] = [7] := by decide
theorem repeated_columns_emit_one_release : released (holdColumns counters [7, 7]) [7, 7] = [7] := by decide
theorem a_shared_column_is_not_released_early :
    released (holdColumns counters [7, 7, 7, 9]) [7, 7] = [] := by decide
theorem naive_per_column_callbacks_are_not_exact : acquired counters [7, 7] ≠ [7, 7] := by decide

end Controls
end Mettapedia.Machines.RelationHoldReceipts
