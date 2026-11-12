import Mettapedia.Machines.Cursor.StampedSnapshots

/-!
# Historical column indexes for stamped snapshot readers

Column chains and membership bits record every issued slot, including rows
retired while a reader may still depend on them. The incremental builder
appends one slot at a time. A query first checks coverage, selects candidates
from its chain or bit vector, and only then applies reader-time visibility.

These are exact-key index algorithms with list representations. Native chain
links, packed words, machine bounds, and their time/space costs need their own
representation refinements. A pending index is not an exhausted query.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.StampedSnapshotsIndex

open StampedSnapshots

variable {Key : Type} [DecidableEq Key]

abbrev Tuple (Key : Type) := List Key

def keyMatch (tuple : Option (Tuple Key)) (column : Nat) (key : Key) : Bool :=
  decide (tuple.bind (fun row => row[column]?) = some key)

def payload (store : Store (Tuple Key)) (id : Nat) : Option (Tuple Key) :=
  (store.row id).map Row.value

def eligibleKey (store : Store (Tuple Key)) (column : Nat) (key : Key) (id : Nat) : Bool :=
  keyMatch (payload store id) column key

structure Index (Key : Type) where
  coverage : Nat
  chain : Nat → Key → List Nat
  bits : Nat → Key → List Bool

def empty : Index Key := ⟨0, fun _ _ => [], fun _ _ => []⟩

/-- One incremental slot load; it does not inspect any reader. -/
def append (index : Index Key) (tuple : Option (Tuple Key)) : Index Key :=
  ⟨index.coverage + 1,
    fun column key => if keyMatch tuple column key then
      index.chain column key ++ [index.coverage] else index.chain column key,
    fun column key => index.bits column key ++ [keyMatch tuple column key]⟩

def desiredChain (store : Store (Tuple Key)) (count column : Nat) (key : Key) : List Nat :=
  (List.range count).filter (eligibleKey store column key)

def desiredBits (store : Store (Tuple Key)) (count column : Nat) (key : Key) : List Bool :=
  (List.range count).map (eligibleKey store column key)

def Valid (store : Store (Tuple Key)) (index : Index Key) : Prop :=
  index.coverage ≤ store.next ∧
    ∀ column key, index.chain column key = desiredChain store index.coverage column key ∧
      index.bits column key = desiredBits store index.coverage column key

theorem valid_empty (store : Store (Tuple Key)) : Valid store empty := by
  exact ⟨Nat.zero_le _, by intro column key; exact ⟨rfl, rfl⟩⟩

def extend (store : Store (Tuple Key)) (index : Index Key) : Index Key :=
  append index (payload store index.coverage)

theorem valid_extend (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (available : index.coverage < store.next) :
    Valid store (extend store index) := by
  refine ⟨by simpa [extend, append] using Nat.succ_le_of_lt available, ?_⟩
  intro column key
  obtain ⟨chain, bits⟩ := valid.2 column key
  constructor
  · simp only [extend, append, chain, desiredChain, List.range_succ, List.filter_append]
    by_cases selected : keyMatch (payload store index.coverage) column key = true
    · simp [selected, eligibleKey]
    · simp [selected, eligibleKey]
  · simp only [extend, append, bits, desiredBits, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, eligibleKey]

/-- The builder can stop after any number of slots. Catching up is explicit;
it does not pretend a partial index covers newly loaded store rows. -/
def loadStep (store : Store (Tuple Key)) (index : Index Key) : Index Key :=
  if index.coverage < store.next then extend store index else index

def load (store : Store (Tuple Key)) : Nat → Index Key → Index Key
  | 0, index => index
  | amount + 1, index => load store amount (loadStep store index)

theorem valid_loadStep (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) : Valid store (loadStep store index) := by
  unfold loadStep
  split
  · exact valid_extend store index valid ‹_›
  · exact valid

theorem valid_load (store : Store (Tuple Key)) (amount : Nat) (index : Index Key)
    (valid : Valid store index) : Valid store (load store amount index) := by
  induction amount generalizing index with
  | zero => exact valid
  | succ amount ih => exact ih _ (valid_loadStep store index valid)

theorem load_coverage (store : Store (Tuple Key)) (amount : Nat) (index : Index Key)
    (valid : Valid store index) :
    (load store amount index).coverage = min (index.coverage + amount) store.next := by
  induction amount generalizing index with
  | zero => simp [load, Nat.min_eq_left valid.1]
  | succ amount ih =>
      rw [load, ih _ (valid_loadStep store index valid)]
      by_cases pending : index.coverage < store.next
      · simp only [loadStep, if_pos pending, extend, append]
        congr 1
        omega
      · have covered := valid.1
        have caughtUp : index.coverage = store.next := by omega
        rw [loadStep, if_neg pending, caughtUp]
        omega

theorem load_all_covered (store : Store (Tuple Key)) :
    (load store store.next empty).coverage = store.next := by
  simpa [empty] using load_coverage store store.next empty (valid_empty store)

theorem matches_add_old (store : Store (Tuple Key)) (tuple : Tuple Key)
    (column : Nat) (key : Key) (id : Nat) (old : id < store.next) :
    eligibleKey (StampedSnapshots.add store tuple) column key id = eligibleKey store column key id := by
  simp only [eligibleKey, payload, add_keeps_old_slot store tuple id old]

theorem matches_remove (store : Store (Tuple Key)) (retired column : Nat) (key : Key) (id : Nat) :
    eligibleKey (remove store retired) column key id = eligibleKey store column key id := by
  simp only [eligibleKey, payload, remove_keeps_payload]

/-- An index may lag behind new rows without becoming invalid for its
covered prefix. Old readers remain eligible; fresh readers must check coverage. -/
theorem valid_under_add (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (tuple : Tuple Key) :
    Valid (StampedSnapshots.add store tuple) index := by
  refine ⟨by simpa [StampedSnapshots.add] using valid.1.trans (Nat.le_succ _), ?_⟩
  intro column key
  obtain ⟨chain, bits⟩ := valid.2 column key
  have same : ∀ id ∈ List.range index.coverage,
      eligibleKey (StampedSnapshots.add store tuple) column key id = eligibleKey store column key id :=
    fun id member => matches_add_old store tuple column key id
      (lt_of_lt_of_le (List.mem_range.mp member) valid.1)
  constructor
  · rw [chain]
    exact (List.filter_congr same).symm
  · rw [bits]
    exact (List.map_congr_left same).symm

/-- Retirement changes stamps but never unlinks historical candidates. -/
theorem valid_under_remove (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (retired : Nat) : Valid (remove store retired) index := by
  refine ⟨by simpa only [remove_next] using valid.1, ?_⟩
  intro column key
  obtain ⟨chain, bits⟩ := valid.2 column key
  have same : eligibleKey (remove store retired) column key = eligibleKey store column key :=
    funext (matches_remove store retired column key)
  simpa only [desiredChain, desiredBits, same] using And.intro chain bits

def bitIds : Nat → List Bool → List Nat
  | _, [] => []
  | offset, bit :: bits =>
      if bit then offset :: bitIds (offset + 1) bits else bitIds (offset + 1) bits

theorem bitIds_map (offset count : Nat) (selected : Nat → Bool) :
    bitIds offset ((List.range' offset count).map selected) =
      (List.range' offset count).filter selected := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
      by_cases found : selected offset = true <;>
        simp [List.range'_succ, bitIds, found, ih]

def chainCandidates (index : Index Key) (reader : Reader) (column : Nat) (key : Key) : List Nat :=
  (index.chain column key).filter (fun id => decide (id < reader.ceiling))

def bitCandidates (index : Index Key) (reader : Reader) (column : Nat) (key : Key) : List Nat :=
  (bitIds 0 (index.bits column key)).filter (fun id => decide (id < reader.ceiling))

theorem filter_range_below (count ceiling : Nat) (within : ceiling ≤ count) :
    (List.range count).filter (fun id => decide (id < ceiling)) = List.range ceiling := by
  induction count with
  | zero => obtain rfl : ceiling = 0 := Nat.eq_zero_of_le_zero within; rfl
  | succ count ih =>
      by_cases lower : ceiling ≤ count
      · rw [List.range_succ, List.filter_append, ih lower]
        simp [show ¬ count < ceiling by omega]
      · have same : ceiling = count + 1 := by omega
        subst ceiling
        apply List.filter_eq_self.mpr
        intro id member
        simpa using List.mem_range.mp member

theorem chain_candidates_exact (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    chainCandidates index reader column key =
      desiredChain store reader.ceiling column key := by
  rw [chainCandidates, (valid.2 column key).1]
  unfold desiredChain
  calc
    ((List.range index.coverage).filter (eligibleKey store column key)).filter
          (fun id => decide (id < reader.ceiling)) =
        ((List.range index.coverage).filter (fun id => decide (id < reader.ceiling))).filter
          (eligibleKey store column key) := by
      simp only [List.filter_filter]
      congr 1
      funext id
      exact Bool.and_comm _ _
    _ = _ := by rw [filter_range_below _ _ covered]

theorem chain_ordered (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (column : Nat) (key : Key) :
    (index.chain column key).Pairwise (· < ·) := by
  rw [(valid.2 column key).1]
  exact List.Pairwise.filter _ List.pairwise_lt_range

theorem bit_candidates_exact (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader)
    (column : Nat) (key : Key) :
    bitCandidates index reader column key = chainCandidates index reader column key := by
  simp only [bitCandidates, (valid.2 column key).2, desiredBits,
    List.range_eq_range', bitIds_map]
  rw [← List.range_eq_range']
  change (desiredChain store index.coverage column key).filter
      (fun id => decide (id < reader.ceiling)) = _
  rw [← (valid.2 column key).1]
  rfl

def selectReply (column : Nat) (key : Key) : Option (Nat × Tuple Key) → Option (Nat × Tuple Key)
  | none => none
  | some (id, tuple) => if keyMatch (some tuple) column key then some (id, tuple) else none

def sourceQuery (store : Store (Tuple Key)) (reader : Reader) (column : Nat) (key : Key) :
    List (Nat × Tuple Key) := (snapshot store reader).filterMap (selectReply column key)

def chainQuery (store : Store (Tuple Key)) (index : Index Key) (reader : Reader)
    (column : Nat) (key : Key) : List (Nat × Tuple Key) :=
  (chainCandidates index reader column key).filterMap (atTime store reader.time)

def bitQuery (store : Store (Tuple Key)) (index : Index Key) (reader : Reader)
    (column : Nat) (key : Key) : List (Nat × Tuple Key) :=
  (bitCandidates index reader column key).filterMap (atTime store reader.time)

theorem selectReply_atTime (store : Store (Tuple Key)) (time column id : Nat) (key : Key) :
    selectReply column key (atTime store time id) =
      if eligibleKey store column key id then atTime store time id else none := by
  cases found : store.row id with
  | none => simp [atTime, found, eligibleKey, payload, keyMatch, selectReply]
  | some row =>
      by_cases visibleNow : visible time row = true <;>
        by_cases selected : keyMatch (some row.value) column key = true <;>
        simp [atTime, found, eligibleKey, payload, selectReply, visibleNow, selected]

/-- Completeness and soundness hold for the reader's entry time, not merely
for the rows live when this query happens to use the index. Equality is ordered. -/
theorem chain_query_exact (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    chainQuery store index reader column key = sourceQuery store reader column key := by
  rw [chainQuery, chain_candidates_exact store index valid reader covered]
  simp only [desiredChain, List.filterMap_filter, sourceQuery, snapshot, List.filterMap_map,
    Function.comp_def, selectReply_atTime]

theorem bit_query_exact (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    bitQuery store index reader column key = sourceQuery store reader column key := by
  rw [bitQuery, bit_candidates_exact store index valid reader]
  exact chain_query_exact store index valid reader covered column key

inductive Query (Key : Type) where
  | pending
  | complete (answers : List (Nat × Tuple Key))
  deriving Repr, DecidableEq

/-- A semantic completed-query observer. Native readers use retained index
state; this list-valued observer is not a requirement to gather at opening. -/
def query (useBits : Bool) (store : Store (Tuple Key)) (index : Index Key)
    (reader : Reader) (column : Nat) (key : Key) : Query Key :=
  if reader.ceiling ≤ index.coverage then
    .complete (if useBits then bitQuery store index reader column key else
      chainQuery store index reader column key)
  else .pending

theorem query_complete_correct (useBits : Bool) (store : Store (Tuple Key)) (index : Index Key)
    (valid : Valid store index) (reader : Reader) (covered : reader.ceiling ≤ index.coverage)
    (column : Nat) (key : Key) :
    query useBits store index reader column key = .complete (sourceQuery store reader column key) := by
  cases useBits <;> simp [query, covered, bit_query_exact store index valid reader covered,
    chain_query_exact store index valid reader covered]

omit [DecidableEq Key] in
theorem query_uncovered_pending (useBits : Bool) (store : Store (Tuple Key)) (index : Index Key)
    (reader : Reader) (uncovered : index.coverage < reader.ceiling) (column : Nat) (key : Key) :
    query useBits store index reader column key = .pending := by
  simp [query, show ¬reader.ceiling ≤ index.coverage by omega]

/-- An old view may install an index after later adds or retirements. Its
entry eligibility is unchanged, and no reader-specific copy is built. -/
theorem source_query_under_write (store : Store (Tuple Key)) (reader : Reader)
    (admissible : Admissible store reader) (tuple : Tuple Key) (retired column : Nat) (key : Key) :
    sourceQuery (remove (StampedSnapshots.add store tuple) retired) reader column key =
      sourceQuery store reader column key := by
  unfold sourceQuery
  rw [snapshot_remove _ _ _ (admissible_add store tuple reader admissible),
    snapshot_add store tuple reader admissible]

end Mettapedia.Machines.Cursor.StampedSnapshotsIndex
