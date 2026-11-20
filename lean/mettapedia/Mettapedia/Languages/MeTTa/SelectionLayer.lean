import Mettapedia.Languages.MeTTa.PatternSelection
import Mettapedia.Machines.Cursor.OccurrenceMerge
import Mettapedia.Machines.Cursor.StampedSnapshotsIndex
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.RuntimePlumbing.DependencyStamps
import Mathlib.Data.Finset.Sort

/-!
# Matching after occurrence selection

An index proposes positions in a fixed read view. The lane owns the attempt
at each position, including opening the row and interpreting equality.
Attempts may return pending work as data. Only a refuted attempt is absent.
Ordered consumers visit each proposed occurrence at most once and retain
equal payloads at different positions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SelectionLayer

open PatternSelection
open Mettapedia.Machines.Cursor
open Mettapedia.Machines.Cursor.StampedSnapshots (Store Reader atTime)

/-- The finite reference for merging overlapping ordered index streams. -/
def positions (streams : List (List Nat)) : List Nat :=
  (OccurrenceMerge.rows streams).sort

theorem positions_ordered (streams : List (List Nat)) :
    (positions streams).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise

theorem mem_positions (streams : List (List Nat)) (position : Nat) :
    position ∈ positions streams ↔ position ∈ streams.flatten := by
  simp [positions, OccurrenceMerge.rows_eq_flatten]

variable {Match Answer : Type}

def Complete (attempt : Nat → Option Match) (view candidates : List Nat) : Prop :=
  ∀ position ∈ view, attempt position ≠ none → position ∈ candidates

private def missed (view candidates : List Nat) (position : Nat) : Bool :=
  decide (position ∈ view ∧ position ∉ candidates)

private theorem missed_sound {attempt : Nat → Option Match} {view candidates : List Nat}
    (complete : Complete attempt view candidates) : Sound attempt (missed view candidates) := by
  intro position skip
  have absent : position ∈ view ∧ position ∉ candidates := by
    simpa only [missed, decide_eq_true_eq] using skip
  by_contra found
  exact absent.2 (complete position absent.1 found)

private theorem candidates_eq_filter {view candidates : List Nat}
    (orderedView : view.Pairwise (· < ·)) (orderedCandidates : candidates.Pairwise (· < ·))
    (inView : candidates ⊆ view) :
    candidates = view.filter (fun position => !missed view candidates position) := by
  apply orderedCandidates.eq_of_mem_iff (orderedView.filter _)
  intro position
  by_cases present : position ∈ view
  · simp [missed, present]
  · have absent : position ∉ candidates := fun member => present (inView member)
    simp [missed, present, absent]

/-- Ordered every-match and first-match selection can share the same index.
Their continuations still see the lane's actual attempt payload. -/
theorem select_eq_of_complete {attempt : Nat → Option Match} (body : Nat → Match → List Answer)
    {view candidates : List Nat} (orderedView : view.Pairwise (· < ·))
    (orderedCandidates : candidates.Pairwise (· < ·)) (inView : candidates ⊆ view)
    (complete : Complete attempt view candidates) :
    selectAll attempt body candidates = selectAll attempt body view ∧
    selectFirst attempt body candidates = selectFirst attempt body view := by
  rw [candidates_eq_filter orderedView orderedCandidates inView]
  exact ⟨selectAll_filter (missed_sound complete) view,
    selectFirst_filter (missed_sound complete) view⟩

section Journal

variable {Key : Type} [DecidableEq Key]

/-- The fallback bucket holds rows whose key has to be obtained by matching.
A caller unable to certify coverage of a column can use the full view. -/
def columnStreams (bits : Bool) (index : StampedSnapshotsIndex.Index (Option Key)) (reader : Reader)
    (column : Nat) (keys : List Key) : List (List Nat) :=
  (none :: keys.map some).map fun key =>
    if bits then StampedSnapshotsIndex.bitCandidates index reader column key
    else StampedSnapshotsIndex.chainCandidates index reader column key

theorem columnStreams_bits_eq (store : Store (List (Option Key)))
    (index : StampedSnapshotsIndex.Index (Option Key)) (valid : StampedSnapshotsIndex.Valid store index)
    (reader : Reader) (column : Nat) (keys : List Key) :
    columnStreams true index reader column keys = columnStreams false index reader column keys := by
  simp [columnStreams, StampedSnapshotsIndex.bit_candidates_exact store index valid]

private theorem columnStreams_eq_chain (store : Store (List (Option Key)))
    (index : StampedSnapshotsIndex.Index (Option Key)) (valid : StampedSnapshotsIndex.Valid store index)
    (reader : Reader) (column : Nat) (keys : List Key) (bits : Bool) :
    columnStreams bits index reader column keys = columnStreams false index reader column keys := by
  cases bits with
  | false => rfl
  | true => exact columnStreams_bits_eq store index valid reader column keys

/-- Logical lane equality may provide several keys. One advertised key
matching the stored projection is sufficient for occurrence completeness. -/
theorem column_record_survives (store : Store (List (Option Key)))
    (index : StampedSnapshotsIndex.Index (Option Key)) (valid : StampedSnapshotsIndex.Valid store index)
    (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (keys : List Key) (bits : Bool) {position : Nat}
    {row : List (Option Key)} (inside : position < reader.ceiling)
    (visible : atTime store reader.time position = some (position, row))
    {key : Option Key} (probed : key ∈ none :: keys.map some)
    (recorded : row[column]? = some key) :
    position ∈ positions (columnStreams bits index reader column keys) := by
  rw [columnStreams_eq_chain store index valid, mem_positions]
  apply List.mem_flatten.mpr
  refine ⟨StampedSnapshotsIndex.chainCandidates index reader column key, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨key, probed, rfl⟩
  · rw [StampedSnapshotsIndex.chain_candidates_exact store index valid reader covered]
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr inside, ?_⟩
    have exactKey : StampedSnapshotsIndex.selectReply column key (atTime store reader.time position) =
        some (position, row) := by
      simp [visible, StampedSnapshotsIndex.selectReply, StampedSnapshotsIndex.keyMatch, recorded]
    rw [StampedSnapshotsIndex.selectReply_atTime, visible] at exactKey
    split at exactKey
    · assumption
    · cases exactKey

theorem column_positions_in_view (store : Store (List (Option Key)))
    (index : StampedSnapshotsIndex.Index (Option Key)) (valid : StampedSnapshotsIndex.Valid store index)
    (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (keys : List Key) (bits : Bool) :
    positions (columnStreams bits index reader column keys) ⊆ List.range reader.ceiling := by
  rw [columnStreams_eq_chain store index valid]
  intro position member
  obtain ⟨stream, belongs, found⟩ := List.mem_flatten.mp ((mem_positions _ _).mp member)
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp belongs
  change position ∈ StampedSnapshotsIndex.chainCandidates index reader column key at found
  rw [StampedSnapshotsIndex.chain_candidates_exact store index valid reader covered] at found
  exact (List.mem_filter.mp found).1

def attemptAt (store : Store (List (Option Key))) (reader : Reader)
    (attempt : Nat → List (Option Key) → Option Match) (position : Nat) : Option Match :=
  (atTime store reader.time position).bind fun (_, row) => attempt position row

theorem column_select_eq (store : Store (List (Option Key)))
    (index : StampedSnapshotsIndex.Index (Option Key)) (valid : StampedSnapshotsIndex.Valid store index)
    (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (keys : List Key) (bits : Bool) (body : Nat → Match → List Answer)
    (attempt : Nat → List (Option Key) → Option Match)
    (complete : ∀ position row, atTime store reader.time position = some (position, row) →
      attempt position row ≠ none → ∃ key ∈ none :: keys.map some, row[column]? = some key) :
    let positions := positions (columnStreams bits index reader column keys)
    let runAttempt := attemptAt store reader attempt
    selectAll runAttempt body positions = selectAll runAttempt body (List.range reader.ceiling) ∧
      selectFirst runAttempt body positions = selectFirst runAttempt body (List.range reader.ceiling) := by
  dsimp only
  apply select_eq_of_complete body List.pairwise_lt_range (positions_ordered _)
    (column_positions_in_view store index valid reader covered column keys bits)
  intro position within found
  cases seen : atTime store reader.time position with
  | none => exact False.elim (found (by simp [attemptAt, seen]))
  | some pair =>
      obtain ⟨id, row⟩ := pair
      have identity : id = position := by
        unfold atTime at seen
        obtain ⟨_, _, returned⟩ := Option.bind_eq_some_iff.mp seen
        split at returned
        · exact (congrArg Prod.fst (Option.some.inj returned)).symm
        · cases returned
      subst id
      have matched : attempt position row ≠ none := by
        simpa [attemptAt, seen] using found
      obtain ⟨key, probed, recorded⟩ := complete position row seen matched
      exact column_record_survives store index valid reader covered column keys bits
        (List.mem_range.mp within) seen probed recorded

/-- A new reader can outrun a partially built index. It then uses the
complete view until the index covers its ceiling. -/
def columnOrScan (index : StampedSnapshotsIndex.Index (Option Key)) (reader : Reader)
    (column : Nat) (keys : List Key) (bits : Bool) : List Nat :=
  if reader.ceiling ≤ index.coverage then positions (columnStreams bits index reader column keys)
  else List.range reader.ceiling

theorem columnOrScan_select_eq (store : Store (List (Option Key)))
    (index : StampedSnapshotsIndex.Index (Option Key)) (valid : StampedSnapshotsIndex.Valid store index)
    (reader : Reader) (column : Nat) (keys : List Key) (bits : Bool) (body : Nat → Match → List Answer)
    (attempt : Nat → List (Option Key) → Option Match)
    (complete : ∀ position row, atTime store reader.time position = some (position, row) →
      attempt position row ≠ none → ∃ key ∈ none :: keys.map some, row[column]? = some key) :
    let tries := attemptAt store reader attempt
    let proposed := columnOrScan index reader column keys bits
    selectAll tries body proposed = selectAll tries body (List.range reader.ceiling) ∧
      selectFirst tries body proposed = selectFirst tries body (List.range reader.ceiling) := by
  dsimp only [columnOrScan]
  split
  · exact column_select_eq store index valid reader ‹_› column keys bits body attempt complete
  · exact ⟨rfl, rfl⟩

end Journal

section CaptureDependencies

open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.RuntimePlumbing

/-- Changes to unobserved cells do not invalidate a compiled probe. The
certificate includes absences and values that determine later key reads. -/
theorem selectAll_validated_probe {Cell Value : Type} [DecidableEq Value]
    (old current : Cell → Value) (build : Program Cell Value (List (List Nat)))
    (attempt : Nat → Option Match) (body : Nat → Match → List Answer)
    (valid : checkReads current (run old build).reads = true) :
    selectAll attempt body (positions (run old build).answer) =
      selectAll attempt body (positions (run current build).answer) := by
  rw [run_eq_of_agrees old current build ((checkReads_iff _ _).mp valid)]

/-- A versioned provider can use just the stamps of the observed cells. -/
theorem selectAll_stamped_probe {Cell Value : Type}
    (old current : DependencyStamps.Memory Cell Value)
    (build : Program Cell Value (List (List Nat)))
    (attempt : Nat → Option Match) (body : Nat → Match → List Answer)
    (advances : DependencyStamps.Advances old current)
    (valid : DependencyStamps.check old current (run old.value build).reads = true) :
    selectAll attempt body (positions (run old.value build).answer) =
      selectAll attempt body (positions (run current.value build).answer) := by
  rw [DependencyStamps.checked_observation old current build advances valid]

end CaptureDependencies

namespace Controls

theorem overlapping_paths_preserve_distinct_occurrences :
    positions [[0, 2], [0, 3]] = [0, 2, 3] := by
  apply (positions_ordered _).eq_of_mem_iff (by decide)
  intro position
  simp [mem_positions, or_left_comm]

private def capturedKey : Mettapedia.Machines.ReadOnlyQuery.Program Nat Nat (List (List Nat)) :=
  .read 0 (fun referent => .read referent (fun value => .pure (if value = 0 then [[]] else [[0]])))

theorem capture_without_validation_can_lose_row :
    let old := fun key : Nat => if key = 0 then 1 else 0
    let current := fun _ : Nat => 1
    have cached := Mettapedia.Machines.ReadOnlyQuery.run old capturedKey
    old 0 = current 0 ∧ positions cached.answer = [] ∧
      positions (Mettapedia.Machines.ReadOnlyQuery.run current capturedKey).answer = [0] ∧
      Mettapedia.Machines.ReadOnlyQuery.checkReads current cached.reads = false := by
  simp [Mettapedia.Machines.ReadOnlyQuery.run, Mettapedia.Machines.ReadOnlyQuery.checkReads,
    capturedKey, positions, OccurrenceMerge.rows]

end Controls

end Mettapedia.Languages.MeTTa.SelectionLayer
