import Mettapedia.Machines.StableNumberCompaction

/-!
# Numbered relation rows and stable renumbering

The reference reads every stored column number through the dictionary. The
worker marks exactly the positively used numbers, compacts the dictionary and
rewrites columns by prefix rank. It preserves the entire decoded row sequence,
not merely its support. Independent occurrence counts show that copied live
hold counters still count the relocated columns.

This models dictionary/tuple contents. Native hash placement, side-chain
mutation, finite-word bounds and allocation/publication remain separate duties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationNumberingCorrespondence

open StableNumberCompaction
open ArenaHeldResources (logHolds logHolds_pos_iff)

variable {Id : Type}

structure Numbered (Id : Type) where
  dictionary : List Id
  rows : List (List Nat)
  deriving DecidableEq

def Numbered.Valid (state : Numbered Id) : Prop :=
  state.dictionary.Nodup ∧ ∀ row ∈ state.rows, ∀ index ∈ row, index < state.dictionary.length

def decode (state : Numbered Id) : List (List (Option Id)) :=
  state.rows.map (List.map (fun index => state.dictionary[index]?))

def liveMask (state : Numbered Id) : List Bool :=
  (List.range state.dictionary.length).map (fun index => decide (0 < logHolds state.rows index))

@[simp] theorem liveMask_length (state : Numbered Id) :
    (liveMask state).length = state.dictionary.length := by simp [liveMask]

theorem liveMask_lookup (state : Numbered Id) (index : Nat) (bounded : index < state.dictionary.length) :
    (liveMask state)[index]? = some (decide (0 < logHolds state.rows index)) := by
  simp [liveMask, bounded]

theorem liveMask_iff (state : Numbered Id) (index : Nat) :
    (liveMask state)[index]? = some true ↔
      index < state.dictionary.length ∧ ∃ row ∈ state.rows, index ∈ row := by
  by_cases bounded : index < state.dictionary.length
  · rw [liveMask_lookup state index bounded]
    simp [bounded, logHolds_pos_iff]
  · simp [bounded]

def renumber (state : Numbered Id) : Numbered Id :=
  ⟨pack (liveMask state) state.dictionary,
    state.rows.map (List.map (rank (liveMask state)))⟩

theorem live_column (state : Numbered Id) (valid : state.Valid) (row : List Nat)
    (member : row ∈ state.rows) (index : Nat) (column : index ∈ row) :
    (liveMask state)[index]? = some true :=
  (liveMask_iff state index).mpr ⟨valid.2 row member index column, row, member, column⟩

theorem renumber_decode (state : Numbered Id) (valid : state.Valid) :
    decode (renumber state) = decode state := by
  simp only [decode, renumber, List.map_map]
  apply List.map_congr_left
  intro row member
  simp only [Function.comp_apply, List.map_map]
  apply List.map_congr_left
  intro index column
  exact relocated_lookup (liveMask state) state.dictionary (liveMask_length state)
    index (live_column state valid row member index column)

theorem renumber_valid (state : Numbered Id) (valid : state.Valid) : (renumber state).Valid := by
  refine ⟨pack_nodup _ _ valid.1, ?_⟩
  intro newRow rowMember newIndex columnMember
  obtain ⟨row, member, rfl⟩ := List.mem_map.mp rowMember
  obtain ⟨index, column, rfl⟩ := List.mem_map.mp columnMember
  have oldBound := valid.2 row member index column
  have looked := relocated_lookup (liveMask state) state.dictionary (liveMask_length state)
    index (live_column state valid row member index column)
  have present : (renumber state).dictionary[rank (liveMask state) index]? = some state.dictionary[index] := by
    simpa [renumber, List.getElem?_eq_getElem oldBound] using looked
  exact (List.getElem?_eq_some_iff.mp present).1

theorem compact_dictionary_exact (state : Numbered Id) (id : Id) :
    id ∈ (renumber state).dictionary ↔
      ∃ row ∈ state.rows, ∃ index ∈ row, state.dictionary[index]? = some id := by
  rw [renumber, pack_mem]
  constructor
  · rintro ⟨index, live, lookup⟩
    obtain ⟨_, row, member, column⟩ := (liveMask_iff state index).mp live
    exact ⟨row, member, index, column, lookup⟩
  · rintro ⟨row, member, index, column, lookup⟩
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    exact ⟨index, (liveMask_iff state index).mpr ⟨bound, row, member, column⟩, lookup⟩

theorem renumber_no_dead (state : Numbered Id) (index : Nat)
    (bounded : index < (renumber state).dictionary.length) :
    ∃ row ∈ (renumber state).rows, index ∈ row := by
  have compactBound : index < (liveMask state).count true := by
    simpa only [renumber, pack_length (liveMask state) state.dictionary (liveMask_length state)] using bounded
  obtain ⟨old, live, same⟩ := rank_surjective (liveMask state) index compactBound
  obtain ⟨_, row, member, column⟩ := (liveMask_iff state old).mp live
  refine ⟨row.map (rank (liveMask state)), List.mem_map.mpr ⟨row, member, rfl⟩, ?_⟩
  exact List.mem_map.mpr ⟨old, column, same⟩

theorem renumber_holds_positive (state : Numbered Id) (index : Nat)
    (bounded : index < (renumber state).dictionary.length) :
    0 < logHolds (renumber state).rows index :=
  (logHolds_pos_iff _ index).mpr (renumber_no_dead state index bounded)

theorem live_rank_injective (mask : List Bool) (first second : Nat)
    (firstLive : mask[first]? = some true) (secondLive : mask[second]? = some true) :
    rank mask first = rank mask second ↔ first = second := by
  constructor
  · intro same
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with less | greater
    · have := rank_strict mask first second firstLive less; omega
    · have := rank_strict mask second first secondLive greater; omega
  · rintro rfl; rfl

theorem row_count_relocated (mask : List Bool) (row : List Nat) (index : Nat)
    (live : mask[index]? = some true) (columns : ∀ column ∈ row, mask[column]? = some true) :
    (row.map (rank mask)).count (rank mask index) = row.count index := by
  induction row with
  | nil => rfl
  | cons first rest ih =>
      have firstLive := columns first (by simp)
      have tail := ih (fun column member => columns column (by simp [member]))
      simp [List.count_cons, live_rank_injective mask first index firstLive live, tail]

theorem hold_count_relocated (state : Numbered Id) (valid : state.Valid) (index : Nat)
    (live : (liveMask state)[index]? = some true) :
    logHolds (renumber state).rows (rank (liveMask state) index) = logHolds state.rows index := by
  simp only [logHolds, renumber, List.map_map]
  congr 1
  apply List.map_congr_left
  intro row member
  exact row_count_relocated (liveMask state) row index live (live_column state valid row member)

/-- The C worker copies old hold counters along with live dictionary entries. -/
def holdArray (state : Numbered Id) : List Nat :=
  (List.range state.dictionary.length).map (logHolds state.rows)

theorem copied_hold_matches_columns (state : Numbered Id) (valid : state.Valid) (index : Nat)
    (live : (liveMask state)[index]? = some true) :
    (pack (liveMask state) (holdArray state))[rank (liveMask state) index]? =
      some (logHolds (renumber state).rows (rank (liveMask state) index)) := by
  rw [hold_count_relocated state valid index live]
  rw [relocated_lookup (liveMask state) (holdArray state) (by simp [holdArray]) index live]
  have bound := ((liveMask_iff state index).mp live).1
  simp [holdArray, bound]

theorem column_test_relocated (mask : List Bool) (row : List Nat) (column index : Nat)
    (live : mask[index]? = some true) (columns : ∀ item ∈ row, mask[item]? = some true) :
    (row.map (rank mask))[column]? = some (rank mask index) ↔ row[column]? = some index := by
  rw [List.getElem?_map]
  cases found : row[column]? with
  | none => simp
  | some item =>
      have itemLive := columns item (List.mem_of_getElem? found)
      simpa only [Option.map_some, Option.some.injEq] using live_rank_injective mask item index itemLive live

/-- Row coordinates of one column's exact candidate set, in source order.
A native reversed side chain can reverse both results; no row is deduplicated. -/
def sidePositions (column index : Nat) : Nat → List (List Nat) → List Nat
  | _, [] => []
  | start, row :: rows =>
      if row[column]? = some index then start :: sidePositions column index (start + 1) rows
      else sidePositions column index (start + 1) rows

theorem side_positions_relocated (mask : List Bool) (rows : List (List Nat)) (column index start : Nat)
    (live : mask[index]? = some true)
    (columns : ∀ row ∈ rows, ∀ item ∈ row, mask[item]? = some true) :
    sidePositions column (rank mask index) start (rows.map (List.map (rank mask))) =
      sidePositions column index start rows := by
  induction rows generalizing start with
  | nil => rfl
  | cons row rows ih =>
      have first := column_test_relocated mask row column index live (columns row (by simp))
      have rest := ih (start + 1) (fun other member => columns other (by simp [member]))
      simp only [List.map_cons, sidePositions, first, rest]

theorem renumber_side_positions (state : Numbered Id) (valid : state.Valid) (column index : Nat)
    (live : (liveMask state)[index]? = some true) :
    sidePositions column (rank (liveMask state) index) 0 (renumber state).rows =
      sidePositions column index 0 state.rows :=
  side_positions_relocated (liveMask state) state.rows column index 0 live (live_column state valid)

/-- Allocation refusal keeps the original dictionary and rows together. -/
def attempt (allocated : Bool) (state : Numbered Id) : Bool × Numbered Id :=
  if allocated then (true, renumber state) else (false, state)

theorem attempt_decode (allocated : Bool) (state : Numbered Id) (valid : state.Valid) :
    decode (attempt allocated state).2 = decode state := by
  cases allocated <;> simp [attempt, renumber_decode state valid]

namespace Controls

def gapped : Numbered Nat := ⟨[8, 7, 6, 9], [[1, 1], [3, 1], [1, 1]]⟩

theorem gapped_valid : gapped.Valid := by simp [Numbered.Valid, gapped]

theorem rows_and_repeated_columns_relocate :
    renumber gapped = ⟨[7, 9], [[0, 0], [1, 0], [0, 0]]⟩ ∧
    pack (liveMask gapped) (holdArray gapped) = [5, 1] := by decide

theorem duplicate_rows_stay_duplicate :
    (decode (renumber gapped)).count [some 7, some 7] = 2 := by decide

theorem side_candidates_keep_duplicate_occurrence_positions :
    sidePositions 0 1 0 gapped.rows = [0, 2] ∧
    sidePositions 0 0 0 (renumber gapped).rows = [0, 2] := by decide

theorem dropping_dictionary_without_columns_changes_meaning :
    decode (⟨(renumber gapped).dictionary, gapped.rows⟩ : Numbered Nat) ≠ decode gapped := by decide

theorem stale_side_entry_is_not_an_admitted_column :
    ¬ (⟨[8, 7], [[2]]⟩ : Numbered Nat).Valid := by simp [Numbered.Valid]

theorem failed_allocation_keeps_both_arrays : attempt false gapped = (false, gapped) := rfl

end Controls
end Mettapedia.Machines.RelationNumberingCorrespondence
