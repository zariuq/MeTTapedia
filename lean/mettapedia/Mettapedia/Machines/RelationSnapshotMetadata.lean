import Mettapedia.Machines.RelationCapturedRoots

/-!
# Native metadata is a separate lifetime from the terms it enumerates

A kept snapshot's header, columns and record cache share one native allocation;
its shared skeleton and owning universe have separate lifetimes. Loading the
root recipe therefore needs those metadata addresses too. Term roots alone
do not provide those leases. A failed metadata load refuses the root census, rather than supplying
an empty root list and permitting collection to continue.

The two heaps here separate native metadata addresses from term identifiers.
Native pointer access and the runtime's lease/registration mechanisms must
realize the supplied protections; no C allocator or synchronization proof is
claimed by these finite-heap laws.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationSnapshotMetadata

open RelationCapturedRoots ResourceOwnership
variable {Id Address Value : Type}

structure Header (Id Address : Type) where
  head : Id
  universeAddress : Address
  spine : Option Address
  arity : Nat
  count : Nat
  columns : List Id
  records : List (Option Id)
  deriving DecidableEq

inductive Payload (Id Address : Type) where
  | header (data : Header Id Address)
  | spine (nodes : List (Node Id))
  | universeObject
  deriving DecidableEq

def Header.view (header : Header Id Address) (spine : List (Node Id)) : Snapshot Id :=
  ⟨header.head, spine, header.arity, header.count, header.columns, header.records⟩

def load (memory : Address → Option (Payload Id Address)) (address : Address) : Option (Snapshot Id) := do
  match ← memory address with
  | .spine _ | .universeObject => none
  | .header header =>
      let .universeObject ← memory header.universeAddress | none
      match header.spine with
      | none => some (header.view [])
      | some pointer =>
          match ← memory pointer with
          | .header _ | .universeObject => none
          | .spine nodes => some (header.view nodes)

def dependencies (memory : Address → Option (Payload Id Address)) (address : Address) : List Address :=
  match memory address with
  | some (.header header) => address :: header.universeAddress :: header.spine.toList
  | _ => [address]

theorem load_agrees (before after : Address → Option (Payload Id Address)) (address : Address)
    (stable : ∀ key ∈ dependencies before address, before key = after key) :
    load before address = load after address := by
  have firstMember : address ∈ dependencies before address := by
    cases found : before address with
    | none => simp [dependencies, found]
    | some payload => cases payload <;> simp [dependencies, found]
  have first : before address = after address := stable address firstMember
  cases found : before address with
  | none => simp [load, ← first, found]
  | some payload =>
      cases payload with
      | spine nodes => simp [load, ← first, found]
      | universeObject => simp [load, ← first, found]
      | header header =>
          have universeSame := stable header.universeAddress (by simp [dependencies, found])
          cases pointer : header.spine with
          | none => simp [load, ← first, found, pointer, universeSame]
          | some target =>
              have same := stable target (by simp [dependencies, found, pointer])
              simp [load, ← first, found, pointer, same, universeSame]

def loadAll (memory : Address → Option (Payload Id Address)) : List Address → Option (List (Snapshot Id))
  | [] => some []
  | address :: rest => do
      let view ← load memory address
      let views ← loadAll memory rest
      pure (view :: views)

theorem loadAll_cons_iff (memory : Address → Option (Payload Id Address)) (address : Address)
    (rest : List Address) (views : List (Snapshot Id)) :
    loadAll memory (address :: rest) = some views ↔
      ∃ view, load memory address = some view ∧
        ∃ tail, loadAll memory rest = some tail ∧ view :: tail = views := by
  cases first : load memory address with
  | none => simp [loadAll, first]
  | some view =>
      cases later : loadAll memory rest <;> simp [loadAll, first, later]

theorem loadAll_length (memory : Address → Option (Payload Id Address)) (addresses : List Address)
    (views : List (Snapshot Id)) (loaded : loadAll memory addresses = some views) :
    views.length = addresses.length := by
  induction addresses generalizing views with
  | nil => cases Option.some.inj loaded; rfl
  | cons address rest ih =>
      rw [loadAll_cons_iff] at loaded
      obtain ⟨view, _, tail, loadedTail, same⟩ := loaded
      subst views
      simpa using congrArg Nat.succ (ih tail loadedTail)

theorem loadAll_contains (memory : Address → Option (Payload Id Address)) (addresses : List Address)
    (views : List (Snapshot Id)) (loaded : loadAll memory addresses = some views)
    (address : Address) (member : address ∈ addresses) :
    ∃ view ∈ views, load memory address = some view := by
  induction addresses generalizing views with
  | nil => simp at member
  | cons first rest ih =>
      rw [loadAll_cons_iff] at loaded
      obtain ⟨view, found, tail, loadedTail, same⟩ := loaded
      subst views
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨view, by simp, found⟩
      · obtain ⟨other, otherMember, same⟩ := ih tail loadedTail later
        exact ⟨other, by simp [otherMember], same⟩

variable [DecidableEq Address]

/-- A registry is scoped to one admitted term universe. Equal raw IDs in a
foreign universe must not be merged into this census. The unscoped loader
above is only the metadata-reading component of this preparation. -/
def prepareCensus (memory : Address → Option (Payload Id Address)) (universeAddress : Address)
    (providers : List Address) : Option (List (Snapshot Id)) :=
  if providers.all (fun address => match memory address with
      | some (.header header) => decide (header.universeAddress = universeAddress)
      | _ => false) then loadAll memory providers else none

theorem prepared_census_complete (memory : Address → Option (Payload Id Address))
    (universeAddress : Address) (providers : List Address) (views : List (Snapshot Id))
    (prepared : prepareCensus memory universeAddress providers = some views) :
    loadAll memory providers = some views ∧
      ∀ address ∈ providers, ∃ header, memory address = some (.header header) ∧
        header.universeAddress = universeAddress := by
  unfold prepareCensus at prepared
  split at prepared
  · rename_i sameUniverse
    refine ⟨prepared, ?_⟩
    intro address member
    have checked := (List.all_eq_true.mp sameUniverse) address member
    cases found : memory address with
    | none => simp [found] at checked
    | some payload =>
        cases payload with
        | spine nodes => simp [found] at checked
        | universeObject => simp [found] at checked
        | header header => exact ⟨header, rfl, by simpa [found] using checked⟩
  · simp at prepared

theorem live_metadata_preserves_load {Owner : Type} (heap : Heap Address (Payload Id Address))
    (address : Address) (allRoots : Roots Owner Address)
    (live : ∀ key ∈ dependencies (RelationRootOwners.heapLookup heap) address, Live heap allRoots key) :
    load (RelationRootOwners.heapLookup (collect heap allRoots)) address =
      load (RelationRootOwners.heapLookup heap) address := by
  symm
  apply load_agrees
  intro key member
  simp only [RelationRootOwners.heapLookup, lookup_collect_of_live heap allRoots (live key member)]

def metadataRoots (memory : Address → Option (Payload Id Address)) (address : Address) : Roots Unit Address :=
  (dependencies memory address).toFinset.image (fun key => ((), key))

theorem metadata_collection_preserves_load (heap : Heap Address (Payload Id Address))
    (address : Address) (allRoots : Roots Unit Address)
    (included : metadataRoots (RelationRootOwners.heapLookup heap) address ⊆ allRoots)
    (allocated : ValidRoots heap (metadataRoots (RelationRootOwners.heapLookup heap) address)) :
    load (RelationRootOwners.heapLookup (collect heap allRoots)) address =
      load (RelationRootOwners.heapLookup heap) address := by
  symm
  apply load_agrees
  intro key member
  have own : ((), key) ∈ metadataRoots (RelationRootOwners.heapLookup heap) address := by
    simp [metadataRoots, member]
  have live := live_of_root heap allRoots (included own) (allocated ((), key) own)
  simp only [RelationRootOwners.heapLookup, lookup_collect_of_live heap allRoots live]

/-- Reuse the existing admitted-use lifetime owner: detaching a descriptor's
current slot does not revoke a previously enrolled reader's memory lease.
The snapshot allocation itself may be held by the outside owners. -/
theorem descriptor_detach_preserves_load {Holder Use : Type} [DecidableEq Use]
    (state : AcquiredUse.State Holder Use Address) (use : Use) (issued : use ∈ state.uses)
    (heap : Heap Address (Payload Id Address)) (address : Address)
    (outside : Roots (Unit ⊕ Use) Address)
    (live : ∀ key ∈ dependencies (RelationRootOwners.heapLookup heap) address,
      Live heap (AcquiredUse.roots state id ∪ outside) key) :
    load (RelationRootOwners.heapLookup
      (collect heap (AcquiredUse.roots (AcquiredUse.detach state).next id ∪ outside))) address =
        load (RelationRootOwners.heapLookup heap) address := by
  apply live_metadata_preserves_load
  intro key member
  have same : rootAddresses (AcquiredUse.roots (AcquiredUse.detach state).next id ∪ outside) =
      rootAddresses (AcquiredUse.roots state id ∪ outside) := by
    simp only [rootAddresses, Finset.image_union]
    rw [show (AcquiredUse.roots (AcquiredUse.detach state).next id).image Prod.snd =
      (AcquiredUse.roots state id).image Prod.snd from AcquiredUse.detach_keeps_rootAddresses state id issued]
  exact (live_congr_rootAddresses heap _ _ same key).mpr (live key member)

variable [DecidableEq Id]

def census (views : List (Snapshot Id)) : Roots Unit Id :=
  views.foldr (fun view rest => RelationCapturedRoots.roots view ∪ rest) ∅

theorem census_covers (views : List (Snapshot Id)) (view : Snapshot Id) (member : view ∈ views) :
    RelationCapturedRoots.roots view ⊆ census views := by
  induction views with
  | nil => simp at member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Finset.subset_union_left
      · exact (ih later).trans Finset.subset_union_right

omit [DecidableEq Address] in
theorem complete_census_preserves_view (memory : Address → Option (Payload Id Address))
    (addresses : List Address) (views : List (Snapshot Id)) (loaded : loadAll memory addresses = some views)
    (address : Address) (member : address ∈ addresses) (view : Snapshot Id)
    (found : load memory address = some view) (valid : view.Valid) (heap : Heap Id Value)
    (outside : Roots Unit Id)
    (allocated : ValidRoots heap (RelationCapturedRoots.roots view)) :
    readFields view (RelationRootOwners.heapLookup (collect heap (census views ∪ outside))) =
      readFields view (RelationRootOwners.heapLookup heap) := by
  obtain ⟨actual, present, lookup⟩ := loadAll_contains memory addresses views loaded address member
  have same : actual = view := Option.some.inj (lookup.symm.trans found)
  subst actual
  exact collection_preserves_fields view valid heap (census views ∪ outside)
    ((census_covers views view present).trans Finset.subset_union_left) allocated

theorem outside_roots_are_not_discarded (views : List (Snapshot Id)) (heap : Heap Id Value)
    (outside : Roots Unit Id) (id : Id) (live : Live heap outside id) :
    (collect heap (census views ∪ outside)).lookup id = heap.lookup id :=
  lookup_collect_of_live heap _ (live_mono heap Finset.subset_union_right live)

def readThrough (memory : Address → Option (Payload Id Address)) (terms : Id → Option Value)
    (address : Address) : Option (Fields Value) := (load memory address).map (fun view => readFields view terms)

theorem metadata_and_term_collection_compose {Holder Use : Type} [DecidableEq Use]
    (state : AcquiredUse.State Holder Use Address) (use : Use) (issued : use ∈ state.uses)
    (native : Heap Address (Payload Id Address)) (address : Address)
    (outside : Roots (Unit ⊕ Use) Address)
    (live : ∀ key ∈ dependencies (RelationRootOwners.heapLookup native) address,
      Live native (AcquiredUse.roots state id ∪ outside) key)
    (universeAddress : Address) (providers : List Address) (views : List (Snapshot Id))
    (prepared : prepareCensus (RelationRootOwners.heapLookup native) universeAddress providers = some views)
    (member : address ∈ providers) (view : Snapshot Id)
    (found : load (RelationRootOwners.heapLookup native) address = some view)
    (valid : view.Valid) (terms : Heap Id Value)
    (termOutside : Roots Unit Id)
    (allocated : ValidRoots terms (RelationCapturedRoots.roots view)) :
    readThrough (RelationRootOwners.heapLookup
        (collect native (AcquiredUse.roots (AcquiredUse.detach state).next id ∪ outside)))
        (RelationRootOwners.heapLookup (collect terms (census views ∪ termOutside))) address =
      readThrough (RelationRootOwners.heapLookup native) (RelationRootOwners.heapLookup terms) address := by
  rw [readThrough, descriptor_detach_preserves_load state use issued native address outside live,
    found, Option.map_some, readThrough, found, Option.map_some]
  have loaded := (prepared_census_complete _ universeAddress providers views prepared).1
  exact congrArg some (complete_census_preserves_view _ providers views loaded address member view found valid terms termOutside allocated)

namespace Controls

def header : Header Nat Nat := ⟨10, 60, some 80, 2, 1, [7, 7], [some 20]⟩
def nativeMemory : Nat → Option (Payload Nat Nat) := fun address =>
  if address = 70 then some (.header header)
  else if address = 80 then some (.spine [⟨2, 11⟩])
  else if address = 60 then some .universeObject else none

theorem native_allocations_are_dependencies : dependencies nativeMemory 70 = [70, 60, 80] := by decide

theorem live_term_ids_do_not_reconstruct_freed_metadata :
    load nativeMemory 70 ≠ load (Function.update nativeMemory 80 none) 70 := by decide

theorem owning_universe_is_a_lifetime_dependency :
    load nativeMemory 70 ≠ load (Function.update nativeMemory 60 none) 70 := by decide

theorem foreign_universe_provider_is_refused :
    (loadAll nativeMemory [70]).isSome = true ∧ prepareCensus nativeMemory 61 [70] = none := by decide

theorem one_failed_provider_refuses_the_whole_census : loadAll nativeMemory [70, 90] = none := by decide

theorem repeated_provider_occurrences_are_not_silently_dropped :
    (loadAll nativeMemory [70, 70]).map List.length = some 2 := by decide

theorem descriptor_retirement_respects_enrolled_reader :
    let state : AcquiredUse.State Nat Nat Nat := ⟨true, {0}, {5}, none, some 80⟩
    (AcquiredUse.detach state).retired = none ∧
      AcquiredUse.readUse 5 (AcquiredUse.detach state).next = some 80 ∧
      AcquiredUse.readHolder 0 (AcquiredUse.detach state).next = none := by decide

theorem final_reader_extracts_descriptor_once :
    let state : AcquiredUse.State Nat Nat Nat := ⟨false, {0}, {5}, none, some 80⟩
    AcquiredUse.releaseUse 5 state = some ⟨⟨false, {0}, ∅, none, none⟩, some 80⟩ ∧
      AcquiredUse.releaseUse 5 (⟨false, {0}, ∅, none, none⟩ : AcquiredUse.State Nat Nat Nat) = none := by decide

end Controls
end Mettapedia.Machines.RelationSnapshotMetadata
