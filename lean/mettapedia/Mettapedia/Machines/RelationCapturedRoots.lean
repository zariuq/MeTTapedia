import Mettapedia.Machines.RelationRootOwners

/-!
# Complete term roots of a kept occurrence snapshot

The native callback visits the head, constructor nodes of the shared skeleton,
the declared column prefix and materialized record-cache entries. The logical
reader below reads the complete supplied fields. Layout validity relates the
prefix-based callback to that reader; missing lookups remain explicit values.

These are term-root laws. The native buffers containing the snapshot and its
borrowed skeleton need their own lifetime protection: enumerating AtomIds is
not ownership of the C allocation containing the enumeration recipe.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationCapturedRoots

open ResourceOwnership
variable {Id Value : Type}

structure Node (Id : Type) where
  arity : Nat
  head : Id
  deriving DecidableEq

structure Snapshot (Id : Type) where
  head : Id
  spine : List (Node Id)
  arity : Nat
  count : Nat
  columns : List Id
  records : List (Option Id)
  deriving DecidableEq

def Snapshot.Valid (view : Snapshot Id) : Prop :=
  view.columns.length = view.count * view.arity ∧ view.records.length = view.count

def spineIds (spine : List (Node Id)) : List Id :=
  spine.filterMap (fun node => if node.arity = 0 then none else some node.head)

def listed (view : Snapshot Id) : List Id :=
  view.head :: (spineIds view.spine ++ view.columns.take (view.count * view.arity) ++
    (view.records.take view.count).filterMap id)

def Required (view : Snapshot Id) (key : Id) : Prop :=
  key = view.head ∨ (∃ node ∈ view.spine, node.arity ≠ 0 ∧ node.head = key) ∨
    key ∈ view.columns ∨ some key ∈ view.records

theorem spineIds_mem (spine : List (Node Id)) (key : Id) :
    key ∈ spineIds spine ↔ ∃ node ∈ spine, node.arity ≠ 0 ∧ node.head = key := by
  simp only [spineIds, List.mem_filterMap]
  constructor
  · rintro ⟨node, member, found⟩
    by_cases hole : node.arity = 0
    · simp [hole] at found
    · exact ⟨node, member, hole, by simpa [hole] using found⟩
  · rintro ⟨node, member, constructorNode, same⟩
    exact ⟨node, member, by simp [constructorNode, same]⟩

theorem listed_exact (view : Snapshot Id) (valid : view.Valid) (key : Id) :
    key ∈ listed view ↔ Required view key := by
  have columns : view.columns.take (view.count * view.arity) = view.columns := by rw [← valid.1]; simp
  have records : view.records.take view.count = view.records := by rw [← valid.2]; simp
  simp [listed, columns, records, spineIds_mem, Required]

structure Fields (Value : Type) where
  head : Option Value
  spine : List (Option Value)
  columns : List (Option Value)
  records : List (Option (Option Value))
  deriving DecidableEq

def readFields (view : Snapshot Id) (lookup : Id → Option Value) : Fields Value :=
  ⟨lookup view.head, (spineIds view.spine).map lookup, view.columns.map lookup,
    view.records.map (Option.map lookup)⟩

theorem reads_agree (view : Snapshot Id) (valid : view.Valid) (before after : Id → Option Value)
    (stable : ∀ id ∈ listed view, before id = after id) : readFields view before = readFields view after := by
  have required : ∀ id, Required view id → before id = after id :=
    fun id needed => stable id ((listed_exact view valid id).mpr needed)
  have head := required view.head (Or.inl rfl)
  have spine : (spineIds view.spine).map before = (spineIds view.spine).map after := by
    apply List.map_congr_left
    intro id member
    exact required id (Or.inr (Or.inl ((spineIds_mem view.spine id).mp member)))
  have columns : view.columns.map before = view.columns.map after := by
    apply List.map_congr_left
    intro id member
    exact required id (Or.inr (Or.inr (Or.inl member)))
  have records : view.records.map (Option.map before) = view.records.map (Option.map after) := by
    apply List.map_congr_left
    intro record member
    cases record with
    | none => rfl
    | some id => simp only [Option.map_some, required id (Or.inr (Or.inr (Or.inr member)))]
  simp only [readFields, head, spine, columns, records]

variable [DecidableEq Id]

def roots (view : Snapshot Id) : Roots Unit Id := (listed view).toFinset.image (fun id => ((), id))

theorem collection_preserves_fields (view : Snapshot Id) (valid : view.Valid)
    (heap : Heap Id Value) (allRoots : Roots Unit Id) (included : roots view ⊆ allRoots)
    (allocated : ValidRoots heap (roots view)) :
    readFields view (RelationRootOwners.heapLookup (collect heap allRoots)) =
      readFields view (RelationRootOwners.heapLookup heap) := by
  apply reads_agree view valid
  intro id member
  have own : ((), id) ∈ roots view := by simp [roots, member]
  have live := live_of_root heap allRoots (included own) (allocated ((), id) own)
  simp only [RelationRootOwners.heapLookup, lookup_collect_of_live heap allRoots live]

theorem collection_preserves_paths (view : Snapshot Id) (heap : Heap Id Value)
    (allRoots : Roots Unit Id) (included : roots view ⊆ allRoots)
    (allocated : ValidRoots heap (roots view)) (id : Id) (member : id ∈ listed view) (path : List Id) :
    walk (collect heap allRoots) id path = walk heap id path := by
  have own : ((), id) ∈ roots view := by simp [roots, member]
  exact walk_collect heap allRoots (live_of_root heap allRoots (included own) (allocated ((), id) own)) path

/-- A registration failure must retain the old owner or stop before publishing
an unrooted view. This operation returns no new registry on refusal. -/
def register (capacity : Bool) (view : Snapshot Id) (registry : Roots Unit Id) : Option (Roots Unit Id) :=
  if capacity then some (registry ∪ roots view) else none

theorem registered_covers (capacity : Bool) (view : Snapshot Id) (before after : Roots Unit Id)
    (accepted : register capacity view before = some after) : roots view ⊆ after := by
  cases capacity with
  | false => simp [register] at accepted
  | true =>
    have same : before ∪ roots view = after := by simpa [register] using accepted
    subst after
    exact Finset.subset_union_right

theorem registered_preserves_fields (capacity : Bool) (view : Snapshot Id) (valid : view.Valid)
    (heap : Heap Id Value) (before after : Roots Unit Id)
    (allocated : ValidRoots heap (roots view)) (accepted : register capacity view before = some after) :
    readFields view (RelationRootOwners.heapLookup (collect heap after)) =
      readFields view (RelationRootOwners.heapLookup heap) :=
  collection_preserves_fields view valid heap after (registered_covers capacity view before after accepted) allocated

/-- Materialization fills an empty cache slot. It does not replace a record
that another cursor may already have observed. The callback reads the updated
snapshot at collection time, rather than caching its old root list. -/
def cacheRecord (view : Snapshot Id) (index : Nat) (record : Id) : Option (Snapshot Id) :=
  if view.records[index]? = some none then
    some { view with records := view.records.set index (some record) }
  else none

theorem cacheRecord_valid (view : Snapshot Id) (valid : view.Valid) (index : Nat) (record : Id)
    (after : Snapshot Id) (cached : cacheRecord view index record = some after) : after.Valid := by
  unfold cacheRecord at cached
  split at cached
  · cases Option.some.inj cached
    simpa [Snapshot.Valid] using valid
  · simp at cached

theorem cached_record_is_listed (view : Snapshot Id) (valid : view.Valid) (index : Nat) (record : Id)
    (after : Snapshot Id) (cached : cacheRecord view index record = some after) : record ∈ listed after := by
  have afterValid := cacheRecord_valid view valid index record after cached
  unfold cacheRecord at cached
  split at cached
  · rename_i emptySlot
    have bounded := (List.getElem?_eq_some_iff.mp emptySlot).1
    cases Option.some.inj cached
    apply (listed_exact _ afterValid record).mpr
    apply Or.inr ∘ Or.inr ∘ Or.inr
    apply List.mem_of_getElem?
    exact List.getElem?_set_self bounded
  · simp at cached

namespace Controls

def snapshot : Snapshot Nat := ⟨10, [⟨2, 11⟩, ⟨0, 999⟩], 2, 1, [7, 7], [some 20]⟩
def meaning : Nat → Option Nat := fun id => some id

theorem all_native_fields_have_roots : listed snapshot = [10, 11, 7, 7, 20] := by decide

theorem hole_padding_is_not_a_root : 999 ∉ listed snapshot := by decide

theorem cached_record_is_not_covered_by_columns_alone :
    readFields snapshot meaning ≠ readFields snapshot (Function.update meaning 20 none) := by decide

theorem incorrect_declared_length_drops_a_needed_root :
    let malformed := { snapshot with count := 0 }
    7 ∉ listed malformed ∧ Required malformed 7 ∧ ¬ malformed.Valid := by
  simp [listed, snapshot, spineIds, Required, Snapshot.Valid]

theorem registration_refusal_returns_no_view_authority :
    register false snapshot (∅ : Roots Unit Nat) = none := rfl

theorem absent_cache_and_dangling_cache_are_distinct :
    (readFields { snapshot with records := [none] } meaning).records ≠
      (readFields snapshot (Function.update meaning 20 none)).records := by decide

theorem caching_changes_the_required_root_list :
    let before := { snapshot with records := [none] }
    20 ∉ listed before ∧ cacheRecord before 0 20 = some snapshot ∧ 20 ∈ listed snapshot := by decide

theorem a_materialized_record_is_not_overwritten : cacheRecord snapshot 0 21 = none := by decide

end Controls
end Mettapedia.Machines.RelationCapturedRoots
