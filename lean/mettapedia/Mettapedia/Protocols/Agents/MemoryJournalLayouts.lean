import Mettapedia.Protocols.Agents.CrossModeMemory

/-!
# Layouts for an agent's shared history

The ordered record is a contract. Implementations can keep a single log,
consecutive immutable segments, or independently stored records with one
published order. A snapshot head commits to that order and its lineage.
The layout below proves the step that preserves it under append. Reading a
head from an external store still requires a durable, coherent capture.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.MemoryJournalLayouts

open CrossModeMemory

universe u
variable {Shard Id Mode Payload Ref Row : Type u}

/-! ## Consecutive segments -/

theorem sealed_segment_preserves_order (segments : List (List Row)) (delta : List Row) :
    (segments ++ [delta]).flatten = segments.flatten ++ delta := by simp

theorem arbitrary_segment_boundary (rows : List Row) (cut : Nat) :
    [rows.take cut, rows.drop cut].flatten = rows := by
  simp

/-! ## Independent storage with an ordered publication index -/

structure Address (Shard Id : Type u) where
  shard : Shard
  offset : Nat
  id : Id
  deriving DecidableEq

structure IndexedLog (Shard Id Mode Payload : Type u) where
  storage : Shard → List (Occurrence Id Mode Payload)
  order : List (Address Shard Id)

def IndexedLog.empty : IndexedLog Shard Id Mode Payload := ⟨fun _ => [], []⟩

def IndexedLog.address (s : IndexedLog Shard Id Mode Payload) (shard : Shard)
    (row : Occurrence Id Mode Payload) : Address Shard Id :=
  ⟨shard, (s.storage shard).length, row.id⟩

/-- The storage append and the ordered reference are one logical publication.
Unpublished storage can be staged before that step. -/
def IndexedLog.append [DecidableEq Shard] (s : IndexedLog Shard Id Mode Payload)
    (shard : Shard) (row : Occurrence Id Mode Payload) : IndexedLog Shard Id Mode Payload :=
  ⟨fun key => if key = shard then (s.storage key) ++ [row] else s.storage key,
    s.order ++ [s.address shard row]⟩

def IndexedLog.read [DecidableEq Id] (s : IndexedLog Shard Id Mode Payload)
    (loc : Address Shard Id) : Option (Occurrence Id Mode Payload) :=
  match (s.storage loc.shard)[loc.offset]? with
  | some row => if row.id = loc.id then some row else none
  | none => none

theorem append_preserves_address [DecidableEq Shard] [DecidableEq Id]
    (s : IndexedLog Shard Id Mode Payload) (shard : Shard)
    (inserted : Occurrence Id Mode Payload) {loc : Address Shard Id}
    {old : Occurrence Id Mode Payload} (h : s.read loc = some old) :
    (s.append shard inserted).read loc = some old := by
  cases found : (s.storage loc.shard)[loc.offset]? with
  | none => simp [IndexedLog.read, found] at h
  | some row =>
    obtain ⟨inBounds, _⟩ := List.getElem?_eq_some_iff.mp found
    have same : ((s.append shard inserted).storage loc.shard)[loc.offset]? = some row := by
      unfold IndexedLog.append
      dsimp only
      split
      · rw [List.getElem?_append_left inBounds, found]
      · exact found
    rw [IndexedLog.read, same]
    simpa only [IndexedLog.read, found] using h

theorem append_resolves_new_address [DecidableEq Shard] [DecidableEq Id]
    (s : IndexedLog Shard Id Mode Payload) (shard : Shard) (row : Occurrence Id Mode Payload) :
    (s.append shard row).read (s.address shard row) = some row := by
  simp [IndexedLog.read, IndexedLog.append, IndexedLog.address]

/-- Resolve a complete ordered slice. A missing reference cannot establish a
complete answer. An earlier captured prefix can still be read independently. -/
def resolve (read : Ref → Option Row) : List Ref → Option (List Row)
  | [] => some []
  | head :: tail => do
    let row ← read head
    let rest ← resolve read tail
    pure (row :: rest)

theorem resolve_preserved {read replace : Ref → Option Row}
    (stable : ∀ loc row, read loc = some row → replace loc = some row)
    {refs : List Ref} {rows : List Row} (ok : resolve read refs = some rows) :
    resolve replace refs = some rows := by
  induction refs generalizing rows with
  | nil => exact ok
  | cons ref refs ih =>
    cases front : read ref with
    | none => simp [resolve, front] at ok
    | some row =>
      cases rest : resolve read refs with
      | none => simp [resolve, front, rest] at ok
      | some tail =>
        simp [resolve, front, rest] at ok
        simp [resolve, stable ref row front, ih rest, ok]

theorem resolve_append {read : Ref → Option Row}
    {front back : List Ref} {first last : List Row}
    (hf : resolve read front = some first) (hb : resolve read back = some last) :
    resolve read (front ++ back) = some (first ++ last) := by
  induction front generalizing first with
  | nil =>
    have empty : [] = first := Option.some.inj hf
    subst first
    simpa using hb
  | cons ref refs ih =>
    cases value : read ref with
    | none => simp [resolve, value] at hf
    | some v =>
      cases tail : resolve read refs with
      | none => simp [resolve, value, tail] at hf
      | some vs =>
        simp [resolve, value, tail] at hf
        simp [resolve, value, ih tail, ← hf]

theorem resolve_drop {read : Ref → Option Row} {refs : List Ref} {rows : List Row}
    (ok : resolve read refs = some rows) (start : Nat) :
    resolve read (refs.drop start) = some (rows.drop start) := by
  induction refs generalizing rows start with
  | nil =>
    have empty : [] = rows := Option.some.inj ok
    subst rows
    simp [resolve]
  | cons ref refs ih =>
    cases start with
    | zero => simpa using ok
    | succ start =>
      cases front : read ref with
      | none => simp [resolve, front] at ok
      | some row =>
        cases rest : resolve read refs with
        | none => simp [resolve, front, rest] at ok
        | some tail =>
          simp [resolve, front, rest] at ok
          simpa [← ok] using ih rest start

def IndexedLog.readThrough [DecidableEq Id] (s : IndexedLog Shard Id Mode Payload)
    (head : Nat) : Option (List (Occurrence Id Mode Payload)) :=
  if head ≤ s.order.length then resolve s.read (s.order.take head) else none

/-- Demand only the payloads in the requested part of the published order. -/
def IndexedLog.readRange [DecidableEq Id] (s : IndexedLog Shard Id Mode Payload)
    (start head : Nat) : Option (List (Occurrence Id Mode Payload)) :=
  if start ≤ head ∧ head ≤ s.order.length then
    resolve s.read ((s.order.take head).drop start)
  else none

theorem read_range_agrees_with_complete_read [DecidableEq Id]
    {s : IndexedLog Shard Id Mode Payload} {start head : Nat}
    {records : List (Occurrence Id Mode Payload)}
    (range : start ≤ head) (ok : s.readThrough head = some records) :
    s.readRange start head = some (records.drop start) := by
  by_cases bound : head ≤ s.order.length
  · simp only [IndexedLog.readThrough, if_pos bound] at ok
    unfold IndexedLog.readRange
    rw [if_pos ⟨range, bound⟩]
    exact resolve_drop ok start
  · simp [IndexedLog.readThrough, bound] at ok

/-- Validate a retained order against the current index. An implementation
can use an authenticated immutable prefix in place of a structural check. -/
def IndexedLog.readPinned [DecidableEq Shard] [DecidableEq Id]
    (s : IndexedLog Shard Id Mode Payload) (ordered : List (Address Shard Id)) :
    Option (List (Occurrence Id Mode Payload)) :=
  if ordered = s.order.take ordered.length then resolve s.read ordered else none

theorem append_preserves_pinned_order [DecidableEq Shard] [DecidableEq Id]
    {s : IndexedLog Shard Id Mode Payload} (shard : Shard) (row : Occurrence Id Mode Payload)
    {ordered : List (Address Shard Id)} {records : List (Occurrence Id Mode Payload)}
    (pinned : s.readPinned ordered = some records) :
    (s.append shard row).readPinned ordered = some records := by
  by_cases exactOrder : ordered = s.order.take ordered.length
  · have bound : ordered.length ≤ s.order.length := by
      have length := congrArg List.length exactOrder
      rw [List.length_take] at length
      omega
    simp only [IndexedLog.readPinned, if_pos exactOrder] at pinned
    have stable : ordered = (s.append shard row).order.take ordered.length := by
      simpa [IndexedLog.append, List.take_append_of_le_length bound] using exactOrder
    simp only [IndexedLog.readPinned, if_pos stable]
    exact resolve_preserved (fun _ _ prior => append_preserves_address s shard row prior) pinned
  · simp [IndexedLog.readPinned, exactOrder] at pinned

theorem append_preserves_captured_read [DecidableEq Shard] [DecidableEq Id]
    {s : IndexedLog Shard Id Mode Payload} (shard : Shard) (row : Occurrence Id Mode Payload)
    {head : Nat} {records : List (Occurrence Id Mode Payload)}
    (captured : s.readThrough head = some records) :
    (s.append shard row).readThrough head = some records := by
  by_cases h : head ≤ s.order.length
  · have longer : head ≤ (s.append shard row).order.length := by
      simp [IndexedLog.append]; omega
    simp only [IndexedLog.readThrough, if_pos h] at captured
    rw [IndexedLog.readThrough, if_pos longer]
    simp only [IndexedLog.append, List.take_append_of_le_length h]
    exact resolve_preserved (fun _ _ prior => append_preserves_address s shard row prior) captured
  · simp [IndexedLog.readThrough, h] at captured

theorem append_extends_complete_history [DecidableEq Shard] [DecidableEq Id]
    {s : IndexedLog Shard Id Mode Payload} (shard : Shard) (row : Occurrence Id Mode Payload)
    {records : List (Occurrence Id Mode Payload)}
    (captured : s.readThrough s.order.length = some records) :
    let next := s.append shard row
    next.readThrough next.order.length = some (records ++ [row]) := by
  simp only [IndexedLog.readThrough, Nat.le_refl, if_true, List.take_length] at captured ⊢
  change resolve (s.append shard row).read (s.order ++ [s.address shard row]) =
    some (records ++ [row])
  exact resolve_append
    (resolve_preserved (fun _ _ prior => append_preserves_address s shard row prior) captured)
    (by simp [resolve, append_resolves_new_address])

theorem published_head_with_missing_index_is_unavailable [DecidableEq Id]
    (s : IndexedLog Shard Id Mode Payload) (head : Nat) (missing : s.order.length < head) :
    s.readThrough head = none := by
  simp [IndexedLog.readThrough, Nat.not_le_of_lt missing]

def indexed [DecidableEq Shard] (place : Occurrence Id Mode Payload → Shard)
    (rows : List (Occurrence Id Mode Payload)) : IndexedLog Shard Id Mode Payload :=
  rows.foldl (fun log row => log.append (place row) row) .empty

private theorem foldl_append_readback [DecidableEq Shard] [DecidableEq Id]
    (place : Occurrence Id Mode Payload → Shard) (rows : List (Occurrence Id Mode Payload))
    (s : IndexedLog Shard Id Mode Payload) (seen : List (Occurrence Id Mode Payload))
    (captured : s.readThrough s.order.length = some seen) :
    let next := rows.foldl (fun log row => log.append (place row) row) s
    next.readThrough next.order.length = some (seen ++ rows) := by
  induction rows generalizing s seen with
  | nil => simpa using captured
  | cons row rows ih =>
    simpa [List.append_assoc] using
      ih (s.append (place row) row) (seen ++ [row])
        (append_extends_complete_history (place row) row captured)

/-- Arbitrary-length histories read back identically for every placement policy. -/
theorem indexed_readback [DecidableEq Shard] [DecidableEq Id]
    (place : Occurrence Id Mode Payload → Shard) (rows : List (Occurrence Id Mode Payload)) :
    let log := indexed place rows
    log.readThrough log.order.length = some rows := by
  simpa only [indexed, List.nil_append] using
    foldl_append_readback place rows .empty [] (by rfl)

/-! ## Derived fact views -/

structure Change (Id Payload : Type u) where
  id : Id
  value : Option Payload

/-- A retirement removes a fact from the current view. The log keeps the
original occurrence and the retirement, so old versions remain readable. -/
def applyChange [DecidableEq Id] (facts : Id → Option Payload) (change : Change Id Payload) :
    Id → Option Payload :=
  fun id => if id = change.id then change.value else facts id

theorem different_keys_commute [DecidableEq Id] (facts : Id → Option Payload)
    (a b : Change Id Payload) (independent : a.id ≠ b.id) :
    applyChange (applyChange facts a) b = applyChange (applyChange facts b) a := by
  funext id
  by_cases ha : id = a.id <;> by_cases hb : id = b.id
  · exact (independent (ha.symm.trans hb)).elim
  · simp only [applyChange, if_pos ha, if_neg hb]
  · simp only [applyChange, if_neg ha, if_pos hb]
  · simp only [applyChange, if_neg ha, if_neg hb]

def queryComplete (predicate : Row → Bool) (observed : Option (List Row)) : Option (List Row) :=
  observed.map (List.filter predicate)

theorem unavailable_index_cannot_certify_absence (predicate : Row → Bool) :
    queryComplete predicate none ≠ some [] := by simp [queryComplete]

/-! ## Discriminating traces -/

private def mixed : List (Occurrence Nat Bool Nat) := [⟨1, true, 7⟩, ⟨2, false, 9⟩, ⟨3, true, 7⟩]
private def byMode : IndexedLog Bool Nat Bool Nat := indexed Occurrence.origin mixed

theorem shard_concatenation_changes_order :
    byMode.storage true ++ byMode.storage false ≠ mixed ∧
    byMode.readThrough 3 = some mixed := by decide

theorem missing_shard_does_not_create_empty_history :
    let unavailable := { byMode with storage := fun key => if key = true then byMode.storage key else [] }
    unavailable.readThrough 3 = none ∧ unavailable.readThrough 1 = some [⟨1, true, 7⟩] := by decide

theorem a_count_does_not_authenticate_order :
    let reordered := { byMode with order := byMode.order.reverse }
    reordered.readThrough 3 = some mixed.reverse ∧ reordered.readPinned byMode.order = none := by
  decide

theorem conflicting_edits_need_order :
    let remember : Change Nat Nat := ⟨1, some 7⟩
    let retire : Change Nat Nat := ⟨1, none⟩
    let empty : Nat → Option Nat := fun _ => none
    applyChange (applyChange empty remember) retire 1 ≠
      applyChange (applyChange empty retire) remember 1 := by decide

#print axioms sealed_segment_preserves_order
#print axioms append_preserves_captured_read
#print axioms append_preserves_pinned_order
#print axioms read_range_agrees_with_complete_read
#print axioms indexed_readback
#print axioms different_keys_commute
#print axioms missing_shard_does_not_create_empty_history

end Mettapedia.Protocols.Agents.MemoryJournalLayouts
