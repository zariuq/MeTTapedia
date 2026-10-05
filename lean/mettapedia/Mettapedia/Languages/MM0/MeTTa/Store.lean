import Mettapedia.Languages.MeTTa.PeTTa.SourcePrimitives

/-!
# MM0 indexed tables in the PeTTa source store

The running service stores declaration tables and local proof vectors as
ordinary `(index value)` rows in private spaces. These laws connect that
representation to ordered native queries, including duplicate detection and
append-only publication. They use the existing source matcher and store.

A table handle denotes its current contents. Cache correctness additionally
requires the declaration's signature to stay fixed within the cache's scope;
handle equality alone does not establish that invariant.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Store

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.MeTTa.PeTTa
open NamedSpaces (Handle)
open SourcePrimitives (State)

def natural (index : Nat) : Atom := .grounded (.int index)

def row (entry : Nat × Atom) : Atom := .expression [natural entry.1, entry.2]

def rows (entries : List (Nat × Atom)) : List Atom := entries.map row

/-- The dense prefix used for local hypotheses and saved conclusions. -/
def enumerate (values : List Atom) (start : Nat := 0) : List (Nat × Atom) :=
  (values.zipIdx start).map Prod.swap

def indexedQuery (entries : List Atom) (index : Nat) : List Atom :=
  SourcePrimitives.query entries (.expression [natural index, .var "value"]) (.var "value")

theorem query_one_row (wanted stored : Nat) (value : Atom) :
    indexedQuery [row (stored, value)] wanted = if wanted = stored then [value] else [] := by
  by_cases same : wanted = stored
  · subst stored
    simp [indexedQuery, SourcePrimitives.query, row, natural, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, applySubst]
  · simp [indexedQuery, SourcePrimitives.query, row, natural, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, same]
    intro equal
    exact same (Int.ofNat.inj equal)

theorem query_indexed_rows (entries : List (Nat × Atom)) (index : Nat) :
    indexedQuery (rows entries) index =
      (entries.filter (fun entry => entry.1 == index)).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨stored, value⟩
      have splitRows : rows ((stored, value) :: rest) = [row (stored, value)] ++ rows rest := rfl
      simp only [indexedQuery, splitRows, SourcePrimitives.query_append] at ⊢
      change indexedQuery [row (stored, value)] index ++ indexedQuery (rows rest) index = _
      rw [query_one_row, ih]
      by_cases same : index = stored
      · subst stored; simp
      · simp [same, Ne.symm same]

theorem query_enumerated_rows (values : List Atom) (start index : Nat) :
    indexedQuery (rows (enumerate values start)) index =
      if start ≤ index then (values[index - start]?).toList else [] := by
  induction values generalizing start with
  | nil => simp [enumerate, rows, indexedQuery, SourcePrimitives.query]
  | cons first rest ih =>
      have splitRows : rows (enumerate (first :: rest) start) =
          [row (start, first)] ++ rows (enumerate rest (start + 1)) := by
        simp [enumerate, rows, List.zipIdx_cons]
      simp only [indexedQuery, splitRows, SourcePrimitives.query_append]
      change indexedQuery [row (start, first)] index ++
        indexedQuery (rows (enumerate rest (start + 1))) index = _
      rw [query_one_row, ih]
      rcases Nat.lt_trichotomy index start with less | same | greater
      · simp [Nat.ne_of_lt less, Nat.not_le.mpr less,
          show ¬ start + 1 ≤ index by omega]
      · subst index
        simp
      · have shift : index - start = (index - (start + 1)) + 1 := by omega
        simp [Ne.symm (Nat.ne_of_lt greater), Nat.le_of_lt greater,
          show start + 1 ≤ index by omega, shift]

theorem query_dense_prefix (values : List Atom) (index : Nat) :
    indexedQuery (rows (enumerate values)) index = (values[index]?).toList := by
  simpa using query_enumerated_rows values 0 index

theorem enumerate_append_one (values : List Atom) (value : Atom) :
    enumerate (values ++ [value]) = enumerate values ++ [(values.length, value)] := by
  simp [enumerate, List.zipIdx_append]

/-- A representation invariant about the actual allocated private space. -/
def Represents (state : State) (handle : Handle) (entries : List (Nat × Atom)) : Prop :=
  state.read handle = some (rows entries)

theorem query_represented (state : State) (handle : Handle) (entries : List (Nat × Atom))
    (represented : Represents state handle entries) (index : Nat) :
    (state.read handle).map (fun stored => indexedQuery stored index) =
      some ((entries.filter (fun entry => entry.1 == index)).map Prod.snd) := by
  rw [represented, Option.map_some, query_indexed_rows]

theorem publish_preserves_representation {before after : State} {handle : Handle}
    {entries : List (Nat × Atom)} {entry : Nat × Atom}
    (represented : Represents before handle entries)
    (inserted : SourcePrimitives.insert before handle (row entry) = some after) :
    Represents after handle (entries ++ [entry]) := by
  obtain ⟨stored, readBefore, readAfter⟩ := SourcePrimitives.insert_reads_back inserted
  have same : stored = rows entries := Option.some.inj (readBefore.symm.trans represented)
  subst stored
  simpa [Represents, rows] using readAfter

theorem publish_preserves_other_table {before after : State} {handle other : Handle}
    {entries : List (Nat × Atom)} {entry : Nat × Atom}
    (represented : Represents before other entries)
    (inserted : SourcePrimitives.insert before handle (row entry) = some after)
    (different : other ≠ handle) : Represents after other entries := by
  unfold Represents at represented ⊢
  rw [SourcePrimitives.insert_read_other inserted different]
  exact represented

theorem fresh_table_is_empty (before : State) :
    Represents (before.allocate []).2 (before.allocate []).1 [] :=
  SourcePrimitives.fresh_handle_reads_empty before

theorem absent_index_returns_no_value (entries : List (Nat × Atom)) (index : Nat)
    (absent : ∀ entry ∈ entries, entry.1 ≠ index) :
    indexedQuery (rows entries) index = [] := by
  rw [query_indexed_rows]
  have filtered : entries.filter (fun entry => entry.1 == index) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    simpa using absent entry member
  rw [filtered]
  rfl

/-! ## Stored occurrences and numeric scope controls -/

theorem one_stored_value (index : Nat) (value : Atom) :
    indexedQuery (rows [(index, value)]) index = [value] := by
  simp [rows, query_one_row]

theorem duplicate_rows_are_visible (index : Nat) (value : Atom) :
    indexedQuery (rows [(index, value), (index, value)]) index = [value, value] := by
  rw [query_indexed_rows]
  simp

theorem another_index_cannot_reuse_value (first second : Nat) (value : Atom)
    (different : first ≠ second) :
    indexedQuery (rows [(first, value)]) second = [] := by
  simp [rows, query_one_row, Ne.symm different]

theorem index_above_machine_word_is_retained (value : Atom) :
    indexedQuery (rows [(18446744073709551616, value)]) 18446744073709551616 = [value] :=
  one_stored_value _ _

end Mettapedia.Languages.MM0.MeTTa.Store
