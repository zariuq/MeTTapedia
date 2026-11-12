import Mettapedia.Machines.Cursor.StampedSnapshotsIndex

/-!
# Index replacement preserves the advanced reader's residual

The whole-entry query law is insufficient for a resumed reader. This adapter
filters candidate IDs by the actual raw-slot position before visibility is
tested. Chain and bit observations therefore agree with the captured entry
snapshot after dropping the already inspected raw prefix. Rebuilding or
extending index coverage does not reset time, ceiling or position.

These list-valued functions are semantic residual observers, not a requirement
to gather candidates at native opening. Native seek/iterator costs and the
separate last-key state of a priority reader are outside this row-order model.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderResidualIndex

open StampedSnapshots StampedSnapshotsIndex

variable {Key : Type} [DecidableEq Key]

def fromPosition (reader : Reader) (ids : List Nat) : List Nat :=
  ids.filter (fun id => decide (reader.position ≤ id))

def chainResidual (store : Store (Tuple Key)) (index : Index Key) (reader : Reader)
    (column : Nat) (key : Key) : List (Nat × Tuple Key) :=
  (fromPosition reader (chainCandidates index reader column key)).filterMap (atTime store reader.time)

def bitResidual (store : Store (Tuple Key)) (index : Index Key) (reader : Reader)
    (column : Nat) (key : Key) : List (Nat × Tuple Key) :=
  (fromPosition reader (bitCandidates index reader column key)).filterMap (atTime store reader.time)

def sourceResidual (store : Store (Tuple Key)) (reader : Reader) (column : Nat) (key : Key) :
    List (Nat × Tuple Key) :=
  (remaining store reader).filterMap (selectReply column key)

theorem filter_range_from (count position : Nat) :
    (List.range count).filter (fun id => decide (position ≤ id)) =
      (List.range count).drop position := by
  induction count with
  | zero => simp
  | succ count ih =>
      by_cases within : position ≤ count
      · rw [List.range_succ, List.filter_append, ih,
          List.drop_append_of_le_length (by simpa using within)]
        simp [within]
      · have past : count + 1 ≤ position := by omega
        have smallEmpty : (List.range count).drop position = [] :=
          List.drop_eq_nil_of_le (by simp; omega)
        have wholeEmpty : ((List.range count) ++ [count]).drop position = [] :=
          List.drop_eq_nil_of_le (by simpa using past)
        rw [List.range_succ, List.filter_append, ih]
        simp [within, smallEmpty, wholeEmpty]

theorem chain_residual_exact (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    chainResidual store index reader column key = sourceResidual store reader column key := by
  rw [chainResidual, chain_candidates_exact store index valid reader covered]
  unfold fromPosition desiredChain
  have commute :
      ((List.range reader.ceiling).filter (eligibleKey store column key)).filter
          (fun id => decide (reader.position ≤ id)) =
        ((List.range reader.ceiling).filter (fun id => decide (reader.position ≤ id))).filter
          (eligibleKey store column key) := by
    simp only [List.filter_filter]
    congr 1
    funext id
    exact Bool.and_comm _ _
  rw [commute, filter_range_from]
  simp only [List.filterMap_filter, sourceResidual, remaining, snapshot, ← List.map_drop,
    List.filterMap_map, Function.comp_def, selectReply_atTime]

theorem bit_residual_exact (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    bitResidual store index reader column key = sourceResidual store reader column key := by
  rw [bitResidual, bit_candidates_exact store index valid reader]
  exact chain_residual_exact store index valid reader covered column key

theorem transfer_preserves_residual (store : Store (Tuple Key)) (old fresh : Index Key)
    (oldValid : Valid store old) (freshValid : Valid store fresh) (reader : Reader)
    (oldCovered : reader.ceiling ≤ old.coverage) (freshCovered : reader.ceiling ≤ fresh.coverage)
    (column : Nat) (key : Key) :
    chainResidual store old reader column key = bitResidual store fresh reader column key := by
  rw [chain_residual_exact store old oldValid reader oldCovered,
    bit_residual_exact store fresh freshValid reader freshCovered]

theorem coverage_extension_keeps_residual (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (amount column : Nat) (key : Key) :
    chainResidual store index reader column key =
      bitResidual store (load store amount index) reader column key := by
  apply transfer_preserves_residual store index (load store amount index) valid
    (valid_load store amount index valid) reader covered
  rw [load_coverage store amount index valid]
  exact covered.trans (Nat.le_min.mpr ⟨Nat.le_add_right _ _, valid.1⟩)

theorem rebuild_keeps_residual (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    chainResidual store index reader column key =
      bitResidual store (load store store.next empty) reader column key := by
  apply transfer_preserves_residual store index (load store store.next empty) valid
    (valid_load store store.next empty (valid_empty store)) reader covered
  rw [load_all_covered]
  exact covered.trans valid.1

theorem source_residual_under_writes (store : Store (Tuple Key)) (reader : Reader)
    (admissible : Admissible store reader) (tuple : Tuple Key) (retired column : Nat) (key : Key) :
    sourceResidual (StampedSnapshots.remove (StampedSnapshots.add store tuple) retired)
        reader column key = sourceResidual store reader column key := by
  unfold sourceResidual remaining
  rw [snapshot_remove _ _ _ (admissible_add store tuple reader admissible),
    snapshot_add store tuple reader admissible]

theorem transfer_after_writes (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (admissible : Admissible store reader) (tuple : Tuple Key) (retired column : Nat) (key : Key)
    (fresh : Index Key)
    (freshValid : Valid (StampedSnapshots.remove (StampedSnapshots.add store tuple) retired) fresh)
    (freshCovered : reader.ceiling ≤ fresh.coverage) :
    chainResidual store index reader column key =
      bitResidual (StampedSnapshots.remove (StampedSnapshots.add store tuple) retired)
        fresh reader column key := by
  rw [chain_residual_exact store index valid reader covered,
    bit_residual_exact _ fresh freshValid reader freshCovered,
    source_residual_under_writes store reader admissible tuple retired column key]

omit [DecidableEq Key] in
theorem atTime_keeps_id (store : Store (Tuple Key)) (time id : Nat)
    (result : Nat × Tuple Key) (found : atTime store time id = some result) : result.1 = id := by
  cases row : store.row id with
  | none => simp [atTime, row] at found
  | some record =>
      by_cases visibleNow : visible time record = true
      · simpa [atTime, row, visibleNow] using congrArg (fun reply => reply.map Prod.fst) found.symm
      · simp [atTime, row, visibleNow] at found

omit [DecidableEq Key] in
/-- A changed index cannot replay an occurrence from before the retained raw
position. The statement concerns IDs, so duplicate payloads do not hide replay. -/
theorem no_replay (store : Store (Tuple Key)) (index : Index Key) (reader : Reader)
    (column : Nat) (key : Key) (result : Nat × Tuple Key)
    (returned : result ∈ chainResidual store index reader column key) :
    reader.position ≤ result.1 := by
  obtain ⟨id, member, found⟩ := List.mem_filterMap.mp returned
  have bound : reader.position ≤ id := by simpa using (List.mem_filter.mp member).2
  rw [atTime_keeps_id store reader.time id result found]
  exact bound

omit [DecidableEq Key] in
theorem bit_no_replay (store : Store (Tuple Key)) (index : Index Key) (reader : Reader)
    (column : Nat) (key : Key) (result : Nat × Tuple Key)
    (returned : result ∈ bitResidual store index reader column key) :
    reader.position ≤ result.1 := by
  obtain ⟨id, member, found⟩ := List.mem_filterMap.mp returned
  have bound : reader.position ≤ id := by simpa using (List.mem_filter.mp member).2
  rw [atTime_keeps_id store reader.time id result found]
  exact bound

end Mettapedia.Machines.Cursor.ReaderResidualIndex
