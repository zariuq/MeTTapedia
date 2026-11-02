import Mettapedia.Machines.RelationWordOwnership

/-!
# Fact counts, column uses and finite counter capacity

The total column volume bounds every ID's occurrence count. A per-row arity
bound gives a sufficient capacity test, while the exact word preflight from
RelationWordOwnership can admit more cases. Distinct three-column facts can
still require more than one use per fact for the same ID. The large control
is proved symbolically from arbitrary-size list laws, not by allocating or
enumerating billions of runtime facts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationOccurrenceBounds

open ArenaHeldResources (logHolds)
open RelationColumnOwnership
open RelationWordOwnership

variable {Id : Type} [DecidableEq Id]

def volume (rows : List (List Id)) : Nat := (rows.map List.length).sum

theorem holds_le_volume (rows : List (List Id)) (id : Id) : logHolds rows id ≤ volume rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have head : row.count id ≤ row.length := List.count_le_length
      simp only [logHolds, volume, List.map_cons, List.sum_cons] at ih ⊢
      omega

omit [DecidableEq Id] in
theorem volume_le_arity (rows : List (List Id)) (arity : Nat)
    (bounded : ∀ row ∈ rows, row.length ≤ arity) : volume rows ≤ arity * rows.length := by
  induction rows with
  | nil => simp [volume]
  | cons row rows ih =>
      have head := bounded row (by simp)
      have tail := ih (fun other member => bounded other (by simp [member]))
      simp only [volume, List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one] at tail ⊢
      omega

theorem inserted_volume_suffices (state : Words Id) (rows : List (List Id)) (row : List Id)
    (valid : (⟨rows, interpret state⟩ : State Id).Valid)
    (capacity : volume (row :: rows) < modulus) : FitsAddition state row := by
  intro id
  have count := holds_le_volume (row :: rows) id
  have represented := valid.2 id
  simp only [interpret] at represented
  simp only [logHolds, List.map_cons, List.sum_cons] at count
  change (state.uses id).toNat + row.count id < modulus
  change (state.uses id).toNat = (rows.map (fun row => row.count id)).sum at represented
  omega

theorem arity_bound_suffices (state : Words Id) (rows : List (List Id)) (row : List Id) (arity : Nat)
    (valid : (⟨rows, interpret state⟩ : State Id).Valid)
    (width : ∀ fact ∈ row :: rows, fact.length ≤ arity)
    (capacity : arity * (rows.length + 1) < modulus) :
    admitWords state row = true := by
  apply (admitWords_iff state row).mpr
  apply inserted_volume_suffices state rows row valid
  have bound := volume_le_arity (row :: rows) arity width
  simpa only [List.length_cons] using lt_of_le_of_lt bound capacity

/-- Each fact is unique, while its first two columns share one ID. -/
def sharedTriples (count : Nat) : List (List (Option Nat)) :=
  (List.range count).map (fun index => [none, none, some index])

theorem sharedTriples_length (count : Nat) : (sharedTriples count).length = count := by
  simp [sharedTriples]

theorem sharedTriples_width (count : Nat) : ∀ row ∈ sharedTriples count, row.length = 3 := by
  intro row member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem sharedTriples_distinct (count : Nat) : (sharedTriples count).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro first second same
  simpa using same

theorem sharedTriples_shared_count (count : Nat) : logHolds (sharedTriples count) none = 2 * count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [sharedTriples, List.range_succ, List.map_append, List.map_singleton,
        logHolds, List.sum_append, List.sum_singleton, List.map_map] at ih ⊢
      simp only [List.count_cons_self, List.count_cons, beq_iff_eq,
        reduceCtorEq, ↓reduceIte, List.count_nil, Nat.zero_add, Nat.add_zero] at ih ⊢
      omega

theorem distinct_fact_count_does_not_bound_column_uses :
    (sharedTriples 2147483648).Nodup ∧
    (sharedTriples 2147483648).length < modulus ∧
    logHolds (sharedTriples 2147483648) none = modulus := by
  refine ⟨sharedTriples_distinct _, ?_, ?_⟩
  · rw [sharedTriples_length]
    decide
  · rw [sharedTriples_shared_count]
    decide

/-- A common prefix and one distinguishing final column give arbitrary
repeated-column pressure without duplicate facts. -/
def prefixRows (copies count : Nat) : List (List (Option Nat)) :=
  (List.range count).map (fun index => List.replicate copies none ++ [some index])

theorem prefixRows_length (copies count : Nat) : (prefixRows copies count).length = count := by
  simp [prefixRows]

theorem prefixRows_width (copies count : Nat) :
    ∀ row ∈ prefixRows copies count, row.length = copies + 1 := by
  intro row member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  simp

theorem prefixRows_distinct (copies count : Nat) : (prefixRows copies count).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro first second same
  simpa using same

theorem prefixRows_shared_count (copies count : Nat) :
    logHolds (prefixRows copies count) none = copies * count := by
  induction count with
  | zero => simp [prefixRows, logHolds]
  | succ count ih =>
      simp [prefixRows, logHolds, List.range_succ, List.map_map, Nat.mul_succ] at ih ⊢
      omega

theorem prefixRows_number_bound (copies count : Nat) :
    (prefixRows copies count).flatten.toFinset.card ≤ count + 1 := by
  have covered : (prefixRows copies count).flatten.toFinset ⊆
      insert none ((List.range count).map some).toFinset := by
    intro id member
    obtain ⟨row, rowMember, column⟩ := List.mem_flatten.mp (List.mem_toFinset.mp member)
    obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp rowMember
    rcases List.mem_append.mp column with repeated | final
    · have same : id = none := (List.mem_replicate.mp repeated).2
      subst id
      simp
    · have same : id = some index := by simpa using final
      subst id
      simpa using indexMember
  have support := Finset.card_le_card covered
  have inserted := Finset.card_insert_le none ((List.range count).map some).toFinset
  have listed : ((List.range count).map some).toFinset.card ≤ count := by
    simpa using List.toFinset_card_le ((List.range count).map some)
  omega

/-- Both the tuple count and the number count fit a three-quarter-loaded
2^30-slot hash table, yet the common ID needs more than 32 bits of uses.
This is a symbolic capacity control, not an allocated runtime workload. -/
theorem eight_columns_cross_word_before_hash_load_limit :
    (prefixRows 7 613566757).Nodup ∧
    (∀ row ∈ prefixRows 7 613566757, row.length = 8) ∧
    4 * (prefixRows 7 613566757).length ≤ 3 * 1073741824 ∧
    4 * (prefixRows 7 613566757).flatten.toFinset.card ≤ 3 * 1073741824 ∧
    modulus < logHolds (prefixRows 7 613566757) none := by
  refine ⟨prefixRows_distinct _ _, prefixRows_width _ _, ?_, ?_, ?_⟩
  · rw [prefixRows_length]
    decide
  · have bound := prefixRows_number_bound 7 613566757
    omega
  · rw [prefixRows_shared_count]
    decide

namespace Controls

theorem two_facts_are_four_uses :
    logHolds (sharedTriples 2) none = 4 ∧ (sharedTriples 2).Nodup := by
  exact ⟨sharedTriples_shared_count 2, sharedTriples_distinct 2⟩

theorem exact_preflight_can_admit_beyond_volume_budget :
    let state : Words Nat := ⟨fun id => if id = 7 ∨ id = 8 then 2147483648 else 0, {7, 8}⟩
    admitWords state [7, 8] = true ∧
      modulus < (state.uses 7).toNat + (state.uses 8).toNat + 2 := by decide

end Controls
end Mettapedia.Machines.RelationOccurrenceBounds
