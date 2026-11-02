import Mettapedia.Machines.ArenaHeldResources
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Exact column ownership of live relation entries

The reference is the existing `ArenaHeldResources.logHolds`: every live row
contributes one use for each column occurrence. The executable bookkeeping
updates one column at a time and takes/releases a single external hold only
at zero crossings. Repeated columns are counted separately.

The counters use naturals. `removeColumns_safe` proves that a represented row
can be removed without decrementing zero; native word-range checks and the
implementation of retain/release callbacks remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationColumnOwnership

open ArenaHeldResources (logHolds logHolds_pos_iff)

variable {Id : Type} [DecidableEq Id]

structure Counters (Id : Type) where
  uses : Id → Nat
  owned : Finset Id

def Counters.Valid (state : Counters Id) : Prop :=
  ∀ id, id ∈ state.owned ↔ 0 < state.uses id

def hold (state : Counters Id) (id : Id) : Counters Id :=
  ⟨Function.update state.uses id (state.uses id + 1),
    if state.uses id = 0 then insert id state.owned else state.owned⟩

def unhold (state : Counters Id) (id : Id) : Counters Id :=
  ⟨Function.update state.uses id (state.uses id - 1),
    if state.uses id = 1 then state.owned.erase id else state.owned⟩

def holdColumns : Counters Id → List Id → Counters Id
  | state, [] => state
  | state, id :: rest => holdColumns (hold state id) rest

def unholdColumns : Counters Id → List Id → Counters Id
  | state, [] => state
  | state, id :: rest => unholdColumns (unhold state id) rest

def SafeRemoval : Counters Id → List Id → Prop
  | _, [] => True
  | state, id :: rest => 0 < state.uses id ∧ SafeRemoval (unhold state id) rest

theorem hold_valid (state : Counters Id) (valid : state.Valid) (id : Id) :
    (hold state id).Valid := by
  intro observed
  by_cases same : observed = id
  · subst observed
    by_cases zero : state.uses id = 0
    · simp [hold, zero]
    · have held := (valid id).mpr (Nat.pos_of_ne_zero zero)
      simp [hold, zero, held]
  · by_cases zero : state.uses id = 0 <;> simpa [hold, zero, same] using valid observed

theorem unhold_valid (state : Counters Id) (valid : state.Valid) (id : Id) :
    (unhold state id).Valid := by
  intro observed
  by_cases same : observed = id
  · subst observed
    by_cases last : state.uses id = 1
    · simp [unhold, last]
    · simp only [unhold, last, ↓reduceIte, Function.update_self]
      rw [valid]
      omega
  · by_cases last : state.uses id = 1 <;> simpa [unhold, last, same] using valid observed

theorem holdColumns_valid (state : Counters Id) (valid : state.Valid) (row : List Id) :
    (holdColumns state row).Valid := by
  induction row generalizing state with
  | nil => exact valid
  | cons id rest ih => exact ih (hold state id) (hold_valid state valid id)

theorem unholdColumns_valid (state : Counters Id) (valid : state.Valid) (row : List Id) :
    (unholdColumns state row).Valid := by
  induction row generalizing state with
  | nil => exact valid
  | cons id rest ih => exact ih (unhold state id) (unhold_valid state valid id)

theorem holdColumns_uses (state : Counters Id) (row : List Id) (observed : Id) :
    (holdColumns state row).uses observed = state.uses observed + row.count observed := by
  induction row generalizing state with
  | nil => simp [holdColumns]
  | cons id rest ih =>
      rw [holdColumns, ih]
      by_cases same : observed = id
      · subst observed; simp [hold, Nat.add_assoc, Nat.add_comm]
      · simp [hold, same, Ne.symm same]

theorem unholdColumns_uses (state : Counters Id) (row : List Id) (observed : Id) :
    (unholdColumns state row).uses observed = state.uses observed - row.count observed := by
  induction row generalizing state with
  | nil => simp [unholdColumns]
  | cons id rest ih =>
      rw [unholdColumns, ih]
      by_cases same : observed = id
      · subst observed; simp [unhold, Nat.sub_sub, Nat.add_comm]
      · simp [unhold, same, Ne.symm same]

theorem unholdColumns_safe (state : Counters Id) (row : List Id)
    (enough : ∀ id, row.count id ≤ state.uses id) : SafeRemoval state row := by
  induction row generalizing state with
  | nil => trivial
  | cons id rest ih =>
      have head := enough id
      simp only [List.count_cons_self] at head
      refine ⟨by omega, ih (unhold state id) ?_⟩
      intro observed
      have bound := enough observed
      by_cases same : observed = id
      · subst observed
        simp only [List.count_cons_self] at bound
        simp only [unhold, Function.update_self]
        omega
      · simpa [unhold, List.count_cons, same, Ne.symm same] using bound

structure State (Id : Type) where
  rows : List (List Id)
  counters : Counters Id

def State.Valid (state : State Id) : Prop :=
  state.counters.Valid ∧ ∀ id, state.counters.uses id = logHolds state.rows id

def empty : State Id := ⟨[], ⟨fun _ => 0, ∅⟩⟩

theorem empty_valid : (empty : State Id).Valid := by simp [empty, State.Valid, Counters.Valid, logHolds]

def insertRow (state : State Id) (row : List Id) : State Id :=
  ⟨row :: state.rows, holdColumns state.counters row⟩

def insertUnique (state : State Id) (row : List Id) : Bool × State Id :=
  if row ∈ state.rows then (false, state) else (true, insertRow state row)

def removeRow (state : State Id) (row : List Id) : Bool × State Id :=
  if row ∈ state.rows then (true, ⟨state.rows.erase row, unholdColumns state.counters row⟩)
  else (false, state)

theorem insertRow_valid (state : State Id) (valid : state.Valid) (row : List Id) :
    (insertRow state row).Valid := by
  refine ⟨holdColumns_valid state.counters valid.1 row, ?_⟩
  intro id
  simp [insertRow, holdColumns_uses, valid.2, logHolds, Nat.add_comm]

theorem logHolds_perm (first second : List (List Id)) (same : first.Perm second) (id : Id) :
    logHolds first id = logHolds second id := by
  exact (same.map (fun row : List Id => row.count id)).sum_eq

theorem logHolds_remove (rows : List (List Id)) (row : List Id) (member : row ∈ rows) (id : Id) :
    logHolds (rows.erase row) id + row.count id = logHolds rows id := by
  have perm := List.perm_cons_erase member
  have counts := logHolds_perm rows (row :: rows.erase row) perm id
  simpa [logHolds, Nat.add_comm] using counts.symm

theorem removeRow_safe (state : State Id) (valid : state.Valid) (row : List Id) (member : row ∈ state.rows) :
    SafeRemoval state.counters row := by
  apply unholdColumns_safe
  intro id
  rw [valid.2]
  have counted := logHolds_remove state.rows row member id
  omega

theorem removeRow_valid (state : State Id) (valid : state.Valid) (row : List Id) :
    (removeRow state row).2.Valid := by
  by_cases member : row ∈ state.rows
  · simp only [removeRow, member, ↓reduceIte, State.Valid]
    refine ⟨unholdColumns_valid state.counters valid.1 row, ?_⟩
    intro id
    rw [unholdColumns_uses, valid.2]
    have counted := logHolds_remove state.rows row member id
    omega
  · simpa [removeRow, member] using valid

theorem insertUnique_valid (state : State Id) (valid : state.Valid) (row : List Id) :
    (insertUnique state row).2.Valid := by
  by_cases member : row ∈ state.rows <;> simp [insertUnique, member, valid, insertRow_valid state valid row]

/-- The external hold denotes existential reachability from a live column,
while the internal count retains occurrence multiplicity. -/
theorem owned_iff_live_column (state : State Id) (valid : state.Valid) (id : Id) :
    id ∈ state.counters.owned ↔ ∃ row ∈ state.rows, id ∈ row := by
  rw [valid.1 id, valid.2 id]
  exact logHolds_pos_iff state.rows id

theorem removal_releases_exactly (state : State Id) (valid : state.Valid) (row : List Id)
    (member : row ∈ state.rows) (id : Id) :
    id ∉ (removeRow state row).2.counters.owned ↔ state.counters.uses id = row.count id := by
  rw [(removeRow_valid state valid row).1 id]
  simp only [removeRow, member, ↓reduceIte, unholdColumns_uses, not_lt]
  have enough := logHolds_remove state.rows row member id
  rw [← valid.2 id] at enough
  omega

namespace Controls

def repeated : State Nat := insertRow empty [7, 7]

theorem one_external_hold_two_columns : repeated.counters.uses 7 = 2 ∧ repeated.counters.owned = {7} := by decide

theorem deleting_repeated_columns_releases_once :
    (removeRow repeated [7, 7]).2.counters.uses 7 = 0 ∧
    (removeRow repeated [7, 7]).2.counters.owned = ∅ := by decide

theorem another_fact_keeps_the_shared_id :
    let state := insertRow repeated [7, 9]
    (removeRow state [7, 7]).2.counters.uses 7 = 1 ∧
    7 ∈ (removeRow state [7, 7]).2.counters.owned := by decide

theorem duplicate_unique_insert_has_no_new_hold :
    (insertUnique repeated [7, 7]).1 = false ∧ (insertUnique repeated [7, 7]).2.counters.uses 7 = 2 := by decide

theorem presence_bits_are_not_column_counts :
    repeated.counters.owned.card = 1 ∧ repeated.counters.uses 7 = 2 := by decide

end Controls
end Mettapedia.Machines.RelationColumnOwnership
