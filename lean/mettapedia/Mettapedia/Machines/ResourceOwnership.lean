import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.GSLT.Dynamics.StoreReachability
import Mettapedia.Algebra.OccurrenceIdentity
import Mettapedia.Logic.LP.FiniteDependencyClosure
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite resource heaps and owner roots

Resources carry payloads, outgoing references and byte weights.  Owners root
addresses; sharing and cycles are permitted.  The reachability judgment is the
existing `StoreReachability.Reach`, instantiated with the concrete heap lookup.
Collection removes precisely unreachable lookup entries.  It preserves complete
cells, finite path observations, and address identity on reachable resources.

Removing an owner removes its roots, not resources shared with another owner.
Transfer and fork change owner labels without changing the reachable graph.
The storage bound concerns the transitive footprint and byte weights: a bound
on the number of roots alone cannot bound memory, as the chain example shows.

This is a sequential finite-heap contract. It does not implement an allocator,
concurrent marker, foreign finalizer, or a discovery procedure for runtime roots.
The executable census reuses finite dependency closure and agrees with rooted
reachability. A runtime tracer must separately realize that computation and
enumerate every strong root.

Copied residuals additionally need an injective address relocation, with
payloads and outgoing references transported together. These conditions imply
preservation and reflection of complete paths and aliases; owner retagging
alone cannot certify a copied continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership

open Mettapedia.GSLT.Dynamics.StoreReachability (Store Reach)

universe uValue uOwner

-- Address inherits `StoreReachability.Store`'s universe; it need not be finite.
variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}

/-- A resource's identity is its heap address, separate from its payload. -/
structure Cell (Address : Type) (Value : Type uValue) where
  value : Value
  references : Finset Address
  bytes : Nat
  deriving DecidableEq

/-- A finite, reference-closed heap.  Unallocated addresses have no cell. -/
structure Heap (Address : Type) (Value : Type uValue) where
  lookup : Address → Option (Cell Address Value)
  allocated : Finset Address
  allocated_iff : ∀ a, a ∈ allocated ↔ ∃ c, lookup a = some c
  closed : ∀ a c, lookup a = some c →
    ∀ b ∈ c.references, b ∈ allocated

/-- Multiple owners may protect the same address. -/
abbrev Roots (Owner : Type uOwner) (Address : Type) := Finset (Owner × Address)

/-- Root addresses already exist in the configuration in which they are used. -/
def ValidRoots (h : Heap Address Value) (roots : Roots Owner Address) : Prop :=
  ∀ pair ∈ roots, pair.2 ∈ h.allocated

variable [DecidableEq Address]

/-- Root labels determine ownership; reachability uses their addresses. -/
def rootAddresses (roots : Roots Owner Address) : Finset Address :=
  roots.image Prod.snd

theorem rootAddresses_subset_iff_validRoots (heap : Heap Address Value)
    (roots : Roots Owner Address) :
    rootAddresses roots ⊆ heap.allocated ↔ ValidRoots heap roots := by
  constructor
  · intro included pair member
    exact included (Finset.mem_image.mpr ⟨pair, member, rfl⟩)
  · intro valid address member
    obtain ⟨pair, present, rfl⟩ := Finset.mem_image.mp member
    exact valid pair present

/-- Inspecting every allocated cell requires an owner for the full snapshot.
This policy differs from retaining only the active computation's roots. -/
def Heap.snapshotRoots [DecidableEq Owner] (heap : Heap Address Value)
    (owner : Owner) : Roots Owner Address :=
  heap.allocated.image fun address => (owner, address)

@[simp] theorem rootAddresses_snapshotRoots [DecidableEq Owner]
    (heap : Heap Address Value) (owner : Owner) :
    rootAddresses (heap.snapshotRoots owner) = heap.allocated := by
  simp [rootAddresses, Heap.snapshotRoots, Finset.image_image]

theorem Heap.snapshotRoots_valid [DecidableEq Owner]
    (heap : Heap Address Value) (owner : Owner) :
    ValidRoots heap (heap.snapshotRoots owner) :=
  (rootAddresses_subset_iff_validRoots heap _).mp (by simp)

/-- Interpret the finite heap in the existing graph reachability semantics. -/
def Heap.toStore (h : Heap Address Value) (roots : Roots Owner Address) :
    Store Address where
  pointsTo a b := ∃ c, h.lookup a = some c ∧ b ∈ c.references
  root a := a ∈ h.allocated ∧ a ∈ rootAddresses roots

abbrev Live (h : Heap Address Value) (roots : Roots Owner Address)
    (a : Address) : Prop := Reach (h.toStore roots) a

theorem live_of_root (h : Heap Address Value) (roots : Roots Owner Address)
    {owner : Owner} {a : Address} (member : (owner, a) ∈ roots)
    (allocated : a ∈ h.allocated) : Live h roots a :=
  .root ⟨allocated, Finset.mem_image.mpr ⟨(owner, a), member, rfl⟩⟩

theorem live_step (h : Heap Address Value) (roots : Roots Owner Address)
    {a b : Address} {c : Cell Address Value} (live : Live h roots a)
    (found : h.lookup a = some c) (reference : b ∈ c.references) :
    Live h roots b :=
  .step live ⟨c, found, reference⟩

theorem live_allocated (h : Heap Address Value) (roots : Roots Owner Address)
    {a : Address} (live : Live h roots a) : a ∈ h.allocated := by
  induction live with
  | root hr => exact hr.1
  | @step a b _ edge _ =>
      obtain ⟨c, found, reference⟩ := edge
      exact h.closed a c found b reference

theorem live_mono (h : Heap Address Value) {roots more : Roots Owner Address}
    (subset : roots ⊆ more) {a : Address} : Live h roots a → Live h more a := by
  intro live
  induction live with
  | root hr =>
      obtain ⟨pair, member, same⟩ := Finset.mem_image.mp hr.2
      exact .root ⟨hr.1, Finset.mem_image.mpr ⟨pair, subset member, same⟩⟩
  | step _ edge ih => exact .step ih edge

theorem live_congr_rootAddresses (h : Heap Address Value)
    (roots more : Roots Owner Address)
    (same : rootAddresses roots = rootAddresses more) (a : Address) :
    Live h roots a ↔ Live h more a := by
  have stores : h.toStore roots = h.toStore more := by
    simp only [Heap.toStore, same]
  simp only [Live, stores]

/-- Every reachable cell has a particular owner-root occurrence as its origin. -/
theorem live_iff_root (h : Heap Address Value) (roots : Roots Owner Address)
    (a : Address) :
    Live h roots a ↔ ∃ pair ∈ roots, Live h {pair} a := by
  constructor
  · intro live
    induction live with
    | @root a hr =>
        obtain ⟨pair, member, same⟩ := Finset.mem_image.mp hr.2
        refine ⟨pair, member, .root ⟨hr.1, ?_⟩⟩
        exact Finset.mem_image.mpr ⟨pair, Finset.mem_singleton_self _, same⟩
    | @step a b _ edge ih =>
        obtain ⟨pair, member, origin⟩ := ih
        exact ⟨pair, member, .step origin edge⟩
  · rintro ⟨pair, member, origin⟩
    exact live_mono h (Finset.singleton_subset_iff.mpr member) origin

theorem not_live_empty (h : Heap Address Value) (a : Address) :
    ¬ Live h (∅ : Roots Owner Address) a := by
  rw [live_iff_root]
  simp

/-- Exact transitive footprint, including every shared or cyclic descendant. -/
noncomputable def footprint (h : Heap Address Value)
    (roots : Roots Owner Address) : Finset Address := by
  classical
  exact h.allocated.filter (Live h roots)

@[simp] theorem mem_footprint (h : Heap Address Value)
    (roots : Roots Owner Address) (a : Address) :
    a ∈ footprint h roots ↔ Live h roots a := by
  classical
  simp only [footprint, Finset.mem_filter]
  exact ⟨And.right, fun live => ⟨live_allocated h roots live, live⟩⟩

/-- Owner labels do not change the complete retained allocation footprint. -/
theorem footprint_congr_rootAddresses (h : Heap Address Value)
    (roots more : Roots Owner Address)
    (same : rootAddresses roots = rootAddresses more) :
    footprint h roots = footprint h more := by
  ext address
  rw [mem_footprint, mem_footprint]
  exact live_congr_rootAddresses h roots more same address

/-- Lookup-derived outgoing addresses. An absent address has no outgoing
references; the reference-closed heap contract rules out absent descendants. -/
def Heap.dependencies (h : Heap Address Value) (a : Address) : Finset Address :=
  ((h.lookup a).map Cell.references).getD ∅

omit [DecidableEq Address] in
theorem Heap.dependencies_closed (h : Heap Address Value) {a : Address}
    (allocated : a ∈ h.allocated) : h.dependencies a ⊆ h.allocated := by
  obtain ⟨cell, found⟩ := (h.allocated_iff a).mp allocated
  simp only [Heap.dependencies, found, Option.map_some, Option.getD_some]
  exact h.closed a cell found

/-- Executable transitive census over the already supplied finite heap. The
ambient address type may be infinite and the reference graph may contain
cycles. Physical runtime-root discovery remains a separate obligation. -/
def census (h : Heap Address Value) (roots : Roots Owner Address) : Finset Address :=
  Mettapedia.Logic.LP.FiniteDependencyClosure.within
    h.dependencies h.allocated (rootAddresses roots)

/-- The executable census depends on root addresses, independently of labels. -/
theorem census_congr_rootAddresses (h : Heap Address Value)
    (roots more : Roots Owner Address)
    (same : rootAddresses roots = rootAddresses more) :
    census h roots = census h more := by
  unfold census
  rw [same]

/-- Exactness of the computed census, against the independent inductive
reachability judgment. Root validity prevents a missing root from being
silently removed by the finite-carrier restriction. -/
theorem mem_census_iff_live (h : Heap Address Value) (roots : Roots Owner Address)
    (valid : ValidRoots h roots) (a : Address) :
    a ∈ census h roots ↔ Live h roots a := by
  have rootsAllocated : rootAddresses roots ⊆ h.allocated := by
    intro address member
    obtain ⟨pair, present, rfl⟩ := Finset.mem_image.mp member
    exact valid pair present
  constructor
  · have included : census h roots ⊆ footprint h roots := by
      apply Mettapedia.Logic.LP.FiniteDependencyClosure.within_least
      · intro address member
        exact (mem_footprint h roots address).mpr (.root ⟨rootsAllocated member, member⟩)
      · intro address member child reference
        have live := (mem_footprint h roots address).mp member
        obtain ⟨cell, found⟩ := (h.allocated_iff address).mp
          (live_allocated h roots live)
        simp only [Heap.dependencies, found, Option.map_some, Option.getD_some] at reference
        exact (mem_footprint h roots child).mpr (live_step h roots live found reference)
    exact fun member => (mem_footprint h roots a).mp (included member)
  · intro live
    induction live with
    | root root =>
        exact Mettapedia.Logic.LP.FiniteDependencyClosure.roots_subset_within
          h.dependencies h.allocated (rootAddresses roots) rootsAllocated root.2
    | @step parent child _ edge ih =>
        obtain ⟨cell, found, reference⟩ := edge
        apply Mettapedia.Logic.LP.FiniteDependencyClosure.within_closed
          h.dependencies h.allocated (rootAddresses roots)
          (fun _ => h.dependencies_closed) ih
        simp only [Heap.dependencies, found, Option.map_some, Option.getD_some]
        exact reference

theorem census_eq_footprint (h : Heap Address Value) (roots : Roots Owner Address)
    (valid : ValidRoots h roots) : census h roots = footprint h roots := by
  ext address
  rw [mem_census_iff_live h roots valid, mem_footprint]

@[simp] theorem census_empty (heap : Heap Address Value) :
    census heap (∅ : Roots Owner Address) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro address member
  exact not_live_empty heap address
    ((mem_census_iff_live heap ∅ (by simp [ValidRoots]) address).mp member)

@[simp] theorem census_snapshotRoots [DecidableEq Owner]
    (heap : Heap Address Value) (owner : Owner) :
    census heap (heap.snapshotRoots owner) = heap.allocated := by
  ext address
  rw [mem_census_iff_live heap _ (heap.snapshotRoots_valid owner)]
  constructor
  · exact live_allocated heap _
  · intro allocated
    exact .root ⟨allocated, by simpa using allocated⟩

/-- Several owners retain the union of their transitive footprints, counting
each shared allocation address only once. -/
theorem footprint_union [DecidableEq Owner] (h : Heap Address Value)
    (first second : Roots Owner Address) :
    footprint h (first ∪ second) = footprint h first ∪ footprint h second := by
  classical
  ext address
  rw [Finset.mem_union, mem_footprint, mem_footprint, mem_footprint]
  constructor
  · intro combined
    obtain ⟨pair, member, live⟩ := (live_iff_root h _ address).mp combined
    rcases Finset.mem_union.mp member with left | right
    · exact Or.inl (live_mono h (Finset.singleton_subset_iff.mpr left) live)
    · exact Or.inr (live_mono h (Finset.singleton_subset_iff.mpr right) live)
  · rintro (left | right)
    · exact live_mono h Finset.subset_union_left left
    · exact live_mono h Finset.subset_union_right right

theorem footprint_mono (h : Heap Address Value) {roots more : Roots Owner Address}
    (subset : roots ⊆ more) : footprint h roots ⊆ footprint h more := by
  intro a member
  exact (mem_footprint h more a).mpr
    (live_mono h subset ((mem_footprint h roots a).mp member))

/-- Restriction physically removes the unreachable cells from lookup. -/
noncomputable def collect (h : Heap Address Value)
    (roots : Roots Owner Address) : Heap Address Value := by
  classical
  refine {
    lookup := fun a => if Live h roots a then h.lookup a else none
    allocated := footprint h roots
    allocated_iff := ?_
    closed := ?_
  }
  · intro a
    by_cases live : Live h roots a
    · simp only [mem_footprint, live, if_pos, true_iff]
      exact (h.allocated_iff a).mp (live_allocated h roots live)
    · simp [live]
  · intro a c found b reference
    split at found
    next live =>
      exact (mem_footprint h roots b).mpr (live_step h roots live found reference)
    next _ => cases found

@[simp] theorem allocated_collect (h : Heap Address Value)
    (roots : Roots Owner Address) : (collect h roots).allocated = footprint h roots := rfl

theorem lookup_collect_of_live (h : Heap Address Value)
    (roots : Roots Owner Address) {a : Address} (live : Live h roots a) :
    (collect h roots).lookup a = h.lookup a := by
  classical
  simp [collect, live]

theorem lookup_collect_of_not_live (h : Heap Address Value)
    (roots : Roots Owner Address) {a : Address} (dead : ¬ Live h roots a) :
    (collect h roots).lookup a = none := by
  classical
  simp [collect, dead]

theorem lookup_collect_none_iff (h : Heap Address Value)
    (roots : Roots Owner Address) (a : Address) :
    (collect h roots).lookup a = none ↔ ¬ Live h roots a := by
  constructor
  · intro absent live
    obtain ⟨c, found⟩ := (h.allocated_iff a).mp (live_allocated h roots live)
    rw [lookup_collect_of_live h roots live, found] at absent
    cases absent
  · exact lookup_collect_of_not_live h roots

/-- Preservation of an allocated lookup requires, and is guaranteed by,
retention of that cell. This concerns complete cells, not only their values. -/
theorem lookup_collect_eq_iff_live (heap : Heap Address Value)
    (roots : Roots Owner Address) {address : Address}
    (allocated : address ∈ heap.allocated) :
    (collect heap roots).lookup address = heap.lookup address ↔
      Live heap roots address := by
  constructor
  · intro same
    by_contra dead
    obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp allocated
    rw [lookup_collect_of_not_live heap roots dead, found] at same
    cases same
  · exact lookup_collect_of_live heap roots

theorem lookup_collect_of_unallocated (heap : Heap Address Value)
    (roots : Roots Owner Address) {address : Address}
    (unallocated : address ∉ heap.allocated) :
    (collect heap roots).lookup address = heap.lookup address := by
  have absent : heap.lookup address = none := by
    cases found : heap.lookup address with
    | none => rfl
    | some cell =>
      exact False.elim (unallocated ((heap.allocated_iff address).mpr ⟨cell, found⟩))
  have dead : ¬ Live heap roots address :=
    fun live => unallocated (live_allocated heap roots live)
  rw [lookup_collect_of_not_live heap roots dead, absent]

/-- A complete heap observer can retain every lookup with snapshot roots.
This intentionally gives up collection of allocated cells while it is held. -/
theorem lookup_collect_snapshotRoots [DecidableEq Owner]
    (heap : Heap Address Value) (owner : Owner) (address : Address) :
    (collect heap (heap.snapshotRoots owner)).lookup address = heap.lookup address := by
  by_cases allocated : address ∈ heap.allocated
  · apply lookup_collect_of_live
    exact .root ⟨allocated, by simpa using allocated⟩
  · exact lookup_collect_of_unallocated heap _ allocated

/-- Preserving every lookup is exactly the policy that retains every allocated
cell. A full heap observer cannot authorize removal of an allocated cell. -/
theorem collect_preserves_all_lookups_iff (heap : Heap Address Value)
    (roots : Roots Owner Address) (valid : ValidRoots heap roots) :
    (collect heap roots).lookup = heap.lookup ↔ census heap roots = heap.allocated := by
  constructor
  · intro same
    ext address
    rw [mem_census_iff_live heap roots valid]
    constructor
    · exact live_allocated heap roots
    · intro allocated
      exact (lookup_collect_eq_iff_live heap roots allocated).mp (congrFun same address)
  · intro allRetained
    funext address
    by_cases allocated : address ∈ heap.allocated
    · exact lookup_collect_of_live heap roots
        ((mem_census_iff_live heap roots valid address).mp (allRetained ▸ allocated))
    · exact lookup_collect_of_unallocated heap roots allocated

/-- Collection computes the same rooted graph reachability, in both directions. -/
theorem live_collect_iff (h : Heap Address Value)
    (roots : Roots Owner Address) (a : Address) :
    Live (collect h roots) roots a ↔ Live h roots a := by
  constructor
  · intro live
    induction live with
    | root hr => exact (mem_footprint h roots _).mp hr.1
    | @step a b _ edge ih =>
        obtain ⟨c, found, reference⟩ := edge
        rw [lookup_collect_of_live h roots ih] at found
        exact live_step h roots ih found reference
  · intro live
    induction live with
    | root hr =>
        exact .root ⟨(mem_footprint h roots _).mpr (.root hr), hr.2⟩
    | @step a b prior edge ih =>
        obtain ⟨c, found, reference⟩ := edge
        exact live_step (collect h roots) roots ih
          ((lookup_collect_of_live h roots prior).trans found) reference

theorem collect_lookup_idempotent (h : Heap Address Value)
    (roots : Roots Owner Address) (a : Address) :
    (collect (collect h roots) roots).lookup a = (collect h roots).lookup a := by
  by_cases live : Live h roots a
  · exact lookup_collect_of_live (collect h roots) roots
      ((live_collect_iff h roots a).mpr live)
  · rw [lookup_collect_of_not_live h roots live]
    exact lookup_collect_of_not_live (collect h roots) roots
      (fun again => live ((live_collect_iff h roots a).mp again))

/-- A finite address path observes complete cells and their identity. -/
def walk (h : Heap Address Value) (a : Address) :
    List Address → Option (Address × Cell Address Value)
  | [] => (h.lookup a).map (fun c => (a, c))
  | b :: rest => (h.lookup a).bind fun c =>
      if b ∈ c.references then walk h b rest else none

/-- A successful finite walk necessarily observes the actual endpoint lookup. -/
theorem walk_success_lookup (heap : Heap Address Value) (path : List Address)
    {start endpoint : Address} {cell : Cell Address Value}
    (success : walk heap start path = some (endpoint, cell)) :
    heap.lookup endpoint = some cell := by
  induction path generalizing start with
  | nil =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          exact found
  | cons next rest ih =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next _ => exact ih success
          next _ => cases success

/-- Following a successful prefix continues from its observed endpoint. -/
theorem walk_append_of_success (heap : Heap Address Value) (path suffix : List Address)
    {start endpoint : Address} {cell : Cell Address Value}
    (success : walk heap start path = some (endpoint, cell)) :
    walk heap start (path ++ suffix) = walk heap endpoint suffix := by
  induction path generalizing start with
  | nil =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          rcases success with ⟨rfl, rfl⟩
          rfl
  | cons next rest ih =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next reference =>
            simpa only [List.cons_append, walk, found, Option.bind_some, if_pos reference] using
              ih success
          next _ => cases success

/-- A reference-closed region retains successful endpoints of all its paths.
An unsuccessful path need not remain inside the region. -/
theorem walk_endpoint_in_closed (heap : Heap Address Value) (region : Finset Address)
    (closed : ∀ a ∈ region, heap.dependencies a ⊆ region) (path : List Address)
    {start endpoint : Address} {cell : Cell Address Value} (root : start ∈ region)
    (success : walk heap start path = some (endpoint, cell)) : endpoint ∈ region := by
  induction path generalizing start with
  | nil =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
          exact success.1 ▸ root
  | cons next rest ih =>
      cases found : heap.lookup start with
      | none => simp [walk, found] at success
      | some initial =>
          simp only [walk, found, Option.bind_some] at success
          split at success
          next reference =>
            apply ih _ success
            apply closed start root
            simpa only [Heap.dependencies, found, Option.map_some, Option.getD_some] using reference
          next _ => cases success

theorem walk_collect (h : Heap Address Value) (roots : Roots Owner Address)
    {a : Address} (live : Live h roots a) (path : List Address) :
    walk (collect h roots) a path = walk h a path := by
  induction path generalizing a with
  | nil => simp only [walk, lookup_collect_of_live h roots live]
  | cons b rest ih =>
      simp only [walk, lookup_collect_of_live h roots live]
      obtain ⟨c, found⟩ := (h.allocated_iff a).mp (live_allocated h roots live)
      simp only [found, Option.bind_some]
      split
      next reference => exact ih (live_step h roots live found reference)
      next _ => rfl

/-- Two successful paths alias when they arrive at the same resource address.
Two failed walks do not count as an alias. -/
def Aliases (h : Heap Address Value) (a : Address) (left : List Address)
    (b : Address) (right : List Address) : Prop :=
  ∃ endpoint, (walk h a left).map Prod.fst = some endpoint ∧
    (walk h b right).map Prod.fst = some endpoint

/-- Collection preserves and reflects aliases, not just payload equality.
Path multiplicity is left in the caller's list. -/
theorem aliases_collect (h : Heap Address Value) (roots : Roots Owner Address)
    {a b : Address} (ha : Live h roots a) (hb : Live h roots b)
    (left right : List Address) :
    Aliases (collect h roots) a left b right ↔ Aliases h a left b right := by
  unfold Aliases
  rw [walk_collect h roots ha, walk_collect h roots hb]

/-! ## Borrowed views across immutable growth and reset

A cache may borrow an immutable graph without becoming another strong owner.
Its caller keeps the region alive during a read; an owner identity and reset
generation qualify reuse. The operational history below permits allocation
without changing old cells, or a reset that replaces the entire heap. The
observation law follows from this history, rather than assuming equal reads.
The C implementation must still realize these growth/reset operations and
validate its semantic dependency key separately.
-/

/-- Allocation may add cells, but cannot mutate any previously allocated cell. -/
def Heap.Extends (before after : Heap Address Value) : Prop :=
  ∀ a cell, before.lookup a = some cell → after.lookup a = some cell

omit [DecidableEq Address] in
theorem Heap.Extends.refl (heap : Heap Address Value) : heap.Extends heap := by
  intro a cell found
  exact found

omit [DecidableEq Address] in
theorem Heap.Extends.trans {first second third : Heap Address Value}
    (one : first.Extends second) (two : second.Extends third) :
    first.Extends third := by
  intro a cell found
  exact two a cell (one a cell found)

/-- Restoring cells outside a collected footprint is immutable growth for all
cells that survived that collection. -/
theorem collect_extends_to_original (heap : Heap Address Value)
    (roots : Roots Owner Address) : (collect heap roots).Extends heap := by
  intro a cell found
  by_cases live : Live heap roots a
  · rwa [lookup_collect_of_live heap roots live] at found
  · rw [lookup_collect_of_not_live heap roots live] at found
    cases found

/-- Immutable growth preserves arbitrary descendant reads, including aliases
and paths around a cycle. Looking only at the root cell would not suffice. -/
theorem Heap.Extends.walk_eq {before after : Heap Address Value}
    (growth : before.Extends after) {a : Address} (valid : a ∈ before.allocated)
    (path : List Address) : walk after a path = walk before a path := by
  induction path generalizing a with
  | nil =>
      obtain ⟨cell, found⟩ := (before.allocated_iff a).mp valid
      simp only [walk, found, growth a cell found]
  | cons b rest ih =>
      obtain ⟨cell, found⟩ := (before.allocated_iff a).mp valid
      simp only [walk, found, growth a cell found, Option.bind_some]
      split
      next reference => exact ih (before.closed a cell found b reference)
      next _ => rfl

namespace RequestBorrow

structure Stamp (Owner : Type uOwner) where
  identity : Owner
  epoch : Nat
  deriving DecidableEq

structure Region (Owner : Type uOwner) (Address : Type) (Value : Type uValue) where
  stamp : Stamp Owner
  heap : Heap Address Value

def reset (region : Region Owner Address Value) (replacement : Heap Address Value) :
    Region Owner Address Value :=
  ⟨⟨region.stamp.identity, region.stamp.epoch + 1⟩, replacement⟩

/-- A region's allowed allocation history; resets may reuse physical addresses. -/
inductive History : Region Owner Address Value → Region Owner Address Value → Prop
  | refl (region) : History region region
  | grow {origin current} (prior : History origin current)
      (next : Heap Address Value) (preserved : current.heap.Extends next) :
      History origin { current with heap := next }
  | reset {origin current} (prior : History origin current)
      (next : Heap Address Value) : History origin (reset current next)

omit [DecidableEq Address] in
theorem History.epoch_mono {origin current : Region Owner Address Value}
    (history : History origin current) : origin.stamp.epoch ≤ current.stamp.epoch := by
  induction history with
  | refl => exact Nat.le_refl _
  | grow _ _ _ ih => exact ih
  | reset _ _ ih => exact Nat.le_trans ih (Nat.le_succ _)

omit [DecidableEq Address] in
/-- Matching generations exclude every intervening reset; old cells therefore
remain immutable even after any number of allocations. -/
theorem History.immutable_of_epoch {origin current : Region Owner Address Value}
    (history : History origin current)
    (same : current.stamp.epoch = origin.stamp.epoch) :
    origin.heap.Extends current.heap := by
  induction history with
  | refl => exact Heap.Extends.refl _
  | grow _ _ preserved ih => exact (ih same).trans preserved
  | reset prior _ _ =>
      have monotone := prior.epoch_mono
      simp only [RequestBorrow.reset] at same
      omega

/-- Paths retain their ordered occurrences. Equal addresses do not erase
duplicates, and the view does not acquire strong roots in the resource heap. -/
structure View (Owner : Type uOwner) (Address : Type) where
  stamp : Stamp Owner
  paths : List (Address × List Address)

/-- Transport an ordered list of reference paths. Root publication may
deduplicate addresses; these observations retain every occurrence. -/
def relocatePaths {DestinationAddress : Type} (address : Address → DestinationAddress)
    (paths : List (Address × List Address)) : List (DestinationAddress × List DestinationAddress) :=
  paths.map fun query => (address query.1, query.2.map address)

/-- The pure generation check precedes the supplied path translation.
The translation's graph and lifetime obligations are checked separately. -/
def View.transportIfCurrent [DecidableEq Owner] {DestinationAddress : Type}
    (view : View Owner Address) (current destination : Stamp Owner)
    (address : Address → DestinationAddress) : Option (View Owner DestinationAddress) :=
  if view.stamp = current then
    some ⟨destination, relocatePaths address view.paths⟩
  else none

omit [DecidableEq Address] in
theorem View.transportIfCurrent_eq_some_iff [DecidableEq Owner] {DestinationAddress : Type}
    (view : View Owner Address) (current destination : Stamp Owner)
    (address : Address → DestinationAddress) (moved : View Owner DestinationAddress) :
    view.transportIfCurrent current destination address = some moved ↔
      view.stamp = current ∧ moved = ⟨destination, relocatePaths address view.paths⟩ := by
  unfold View.transportIfCurrent
  by_cases issued : view.stamp = current <;> simp [issued, eq_comm]

omit [DecidableEq Address] in
theorem View.transportIfCurrent_none_iff [DecidableEq Owner] {DestinationAddress : Type}
    (view : View Owner Address) (current destination : Stamp Owner)
    (address : Address → DestinationAddress) :
    view.transportIfCurrent current destination address = none ↔ view.stamp ≠ current := by
  unfold View.transportIfCurrent
  by_cases issued : view.stamp = current <;> simp [issued]

omit [DecidableEq Address] in
theorem View.transportIfCurrent_foreign_rejected [DecidableEq Owner]
    {DestinationAddress : Type} (view : View Owner Address)
    (current destination : Stamp Owner) (address : Address → DestinationAddress)
    (different : view.stamp.identity ≠ current.identity) :
    view.transportIfCurrent current destination address = none := by
  apply (view.transportIfCurrent_none_iff _ _ _).mpr
  exact fun equal => different (congrArg Stamp.identity equal)

omit [DecidableEq Address] in
theorem View.transportIfCurrent_reset_rejected [DecidableEq Owner]
    {DestinationAddress : Type} (view : View Owner Address)
    (current destination : Stamp Owner) (address : Address → DestinationAddress)
    (issued : view.stamp = current) :
    view.transportIfCurrent { current with epoch := current.epoch + 1 }
      destination address = none := by
  apply (view.transportIfCurrent_none_iff _ _ _).mpr
  intro equal
  have epochs := congrArg Stamp.epoch (issued.symm.trans equal)
  simp only at epochs
  omega

def observe (heap : Heap Address Value) (paths : List (Address × List Address)) :
    List (Option (Address × Cell Address Value)) :=
  paths.map fun query => walk heap query.1 query.2

/-- Check retention against the supplied complete reference graph. The starts
may name continuation cells or borrowed services. Duplicate starts are one
storage obligation; their ordered observations remain separate.

The checker neither discovers runtime edges nor grants operation authority.
Mutable services require a separate read/transition contract. -/
def retentionCheck (heap : Heap Address Value) (roots : Roots Owner Address)
    (captured : List Address) : Bool :=
  decide (rootAddresses roots ⊆ heap.allocated) &&
    decide (captured.toFinset ⊆ census heap roots)

/-- Computed coverage is checked against inductive graph liveness, including
transitive dependencies rather than only the captured top cells. -/
theorem retentionCheck_iff (heap : Heap Address Value) (roots : Roots Owner Address)
    (captured : List Address) :
    retentionCheck heap roots captured = true ↔
      ValidRoots heap roots ∧ ∀ start ∈ captured, Live heap roots start := by
  simp only [retentionCheck, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨allocated, covered⟩
    have valid := (rootAddresses_subset_iff_validRoots heap roots).mp allocated
    refine ⟨valid, ?_⟩
    intro start member
    exact (mem_census_iff_live heap roots valid start).mp
      (covered (List.mem_toFinset.mpr member))
  · rintro ⟨valid, live⟩
    refine ⟨(rootAddresses_subset_iff_validRoots heap roots).mpr valid, ?_⟩
    intro start member
    exact (mem_census_iff_live heap roots valid start).mpr
      (live start (List.mem_toFinset.mp member))

/-- For allocated captures, the executable retention checker exactly decides
valid roots and preservation of all requested complete lookups. -/
theorem retentionCheck_iff_preserves_lookups (heap : Heap Address Value)
    (roots : Roots Owner Address) (captured : List Address)
    (allocated : ∀ address ∈ captured, address ∈ heap.allocated) :
    retentionCheck heap roots captured = true ↔
      ValidRoots heap roots ∧ ∀ address ∈ captured,
        (collect heap roots).lookup address = heap.lookup address := by
  rw [retentionCheck_iff]
  constructor
  · rintro ⟨valid, live⟩
    exact ⟨valid, fun address member => lookup_collect_of_live heap roots (live address member)⟩
  · rintro ⟨valid, same⟩
    exact ⟨valid, fun address member =>
      (lookup_collect_eq_iff_live heap roots (allocated address member)).mp (same address member)⟩

theorem retentionCheck_congr_rootAddresses (heap : Heap Address Value)
    (roots more : Roots Owner Address)
    (same : rootAddresses roots = rootAddresses more) (captured : List Address) :
    retentionCheck heap roots captured = retentionCheck heap more captured := by
  unfold retentionCheck
  rw [same, census_congr_rootAddresses heap roots more same]

/-- Every dependency reached from a checked capture is retained. Cycles and
shared descendants need no per-owner duplication. -/
theorem retentionCheck_protects_descendants (heap : Heap Address Value)
    (roots : Roots Owner Address) (captured : List Address)
    (checked : retentionCheck heap roots captured = true)
    {start destination : Address} (member : start ∈ captured)
    (dependency : Live heap ({((), start)} : Roots Unit Address) destination) :
    Live heap roots destination := by
  have retained := (retentionCheck_iff heap roots captured).mp checked
  induction dependency with
  | root hr =>
    have same := hr.2
    simp only [rootAddresses, Finset.image_singleton, Finset.mem_singleton] at same
    simpa only [same] using retained.2 start member
  | step _ edge ih => exact .step ih edge

theorem retentionCheck_preserves_descendant_cell (heap : Heap Address Value)
    (roots : Roots Owner Address) (captured : List Address)
    (checked : retentionCheck heap roots captured = true)
    {start destination : Address} (member : start ∈ captured)
    (dependency : Live heap ({((), start)} : Roots Unit Address) destination) :
    (collect heap roots).lookup destination = heap.lookup destination :=
  lookup_collect_of_live heap roots
    (retentionCheck_protects_descendants heap roots captured checked member dependency)

/-- Exact complete path observations survive collection, including failed
reads, repetitions and emission order. The captured list is a coverage
boundary; it is not an answer-occurrence quotient. -/
theorem retentionCheck_preserves_paths (heap : Heap Address Value)
    (roots : Roots Owner Address) (captured : List Address)
    (checked : retentionCheck heap roots captured = true)
    (paths : List (Address × List Address))
    (covered : ∀ query ∈ paths, query.1 ∈ captured) :
    observe (collect heap roots) paths = observe heap paths := by
  have retained := (retentionCheck_iff heap roots captured).mp checked
  apply List.map_congr_left
  intro query member
  exact walk_collect heap roots (retained.2 query.1 (covered query member)) query.2

def read [DecidableEq Owner] (region : Region Owner Address Value)
    (view : View Owner Address) : Option (List (Option (Address × Cell Address Value))) :=
  if view.stamp = region.stamp then some (observe region.heap view.paths) else none

/-- A successful generation check recovers the original complete observations
from the permitted allocation history, without materializing another graph. -/
theorem read_exact [DecidableEq Owner]
    {origin current : Region Owner Address Value} (history : History origin current)
    (view : View Owner Address) (issued : view.stamp = origin.stamp)
    (currentStamp : view.stamp = current.stamp)
    (valid : ∀ query ∈ view.paths, query.1 ∈ origin.heap.allocated) :
    read current view = some (observe origin.heap view.paths) := by
  have epochs : current.stamp.epoch = origin.stamp.epoch :=
    congrArg Stamp.epoch (currentStamp.symm.trans issued)
  have immutable := history.immutable_of_epoch epochs
  simp only [read, if_pos currentStamp]
  congr 1
  apply List.map_congr_left
  intro query member
  exact immutable.walk_eq (valid query member) query.2

theorem read_reset_rejected [DecidableEq Owner]
    (region : Region Owner Address Value) (replacement : Heap Address Value)
    (view : View Owner Address) (issued : view.stamp = region.stamp) :
    read (reset region replacement) view = none := by
  have different : view.stamp ≠ (reset region replacement).stamp := by
    intro equal
    have epochs := congrArg Stamp.epoch (issued.symm.trans equal)
    simp only [reset] at epochs
    omega
  simp only [read, if_neg different]

theorem read_foreign_rejected [DecidableEq Owner]
    (region : Region Owner Address Value) (view : View Owner Address)
    (different : view.stamp.identity ≠ region.stamp.identity) :
    read region view = none := by
  have unequal : view.stamp ≠ region.stamp :=
    fun equal => different (congrArg Stamp.identity equal)
  simp only [read, if_neg unequal]

end RequestBorrow

/-! ## Relocation into independent storage -/

section Relocation

universe uDestinationValue
variable {DestinationAddress : Type} {DestinationValue : Type uDestinationValue}
variable [DecidableEq DestinationAddress] [DecidableEq Owner]

/-- Complete cell transport keeps reference identity separate from payload
interpretation. Incoming aliases are retained by the injective address map. -/
def Cell.relocate (address : Address → DestinationAddress)
    (payload : Value → DestinationValue) (cell : Cell Address Value) :
    Cell DestinationAddress DestinationValue :=
  ⟨payload cell.value, cell.references.image address, cell.bytes⟩

/-- Rename the actual finite heap lookup and its outgoing addresses. The
inverse names supply lookup; no second graph or assumed observation is used.
The map may move private addresses while fixing a borrowed region. -/
def Heap.relabel (heap : Heap Address Value) (names : Address ≃ DestinationAddress)
    (payload : Value → DestinationValue) : Heap DestinationAddress DestinationValue where
  lookup a := (heap.lookup (names.symm a)).map (Cell.relocate names payload)
  allocated := heap.allocated.image names
  allocated_iff a := by
    constructor
    · intro present
      obtain ⟨original, allocated, rfl⟩ := Finset.mem_image.mp present
      obtain ⟨cell, found⟩ := (heap.allocated_iff original).mp allocated
      exact ⟨cell.relocate names payload, by simp only [names.symm_apply_apply, found,
        Option.map_some]⟩
    · rintro ⟨cell, found⟩
      obtain ⟨original, lookedUp, _⟩ := Option.map_eq_some_iff.mp found
      exact Finset.mem_image.mpr ⟨names.symm a,
        (heap.allocated_iff _).mpr ⟨original, lookedUp⟩, names.apply_symm_apply a⟩
  closed a cell found next reference := by
    obtain ⟨original, lookedUp, same⟩ := Option.map_eq_some_iff.mp found
    rw [← same] at reference
    obtain ⟨previous, edge, rfl⟩ := Finset.mem_image.mp reference
    exact Finset.mem_image.mpr ⟨previous,
      heap.closed (names.symm a) original lookedUp previous edge, rfl⟩

/-- A checked copy agrees at every relocated source address. Destination
storage outside that image is allowed. Root discovery and admission of the
host's semantic authority remain separate runtime obligations. -/
structure Relocation (source : Heap Address Value)
    (destination : Heap DestinationAddress DestinationValue) where
  address : Address → DestinationAddress
  payload : Value → DestinationValue
  injective : Function.Injective address
  lookup_eq : ∀ a, destination.lookup (address a) =
    (source.lookup a).map (Cell.relocate address payload)

/-- The concrete relabeled heap satisfies the complete relocation contract. -/
def Relocation.ofEquiv (source : Heap Address Value) (names : Address ≃ DestinationAddress)
    (payload : Value → DestinationValue) : Relocation source (source.relabel names payload) where
  address := names
  payload := payload
  injective := names.injective
  lookup_eq a := by simp only [Heap.relabel, names.symm_apply_apply]

def Relocation.roots {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) :
    Roots Owner DestinationAddress :=
  roots.image fun pair => (pair.1, copy.address pair.2)

theorem Relocation.rootAddresses {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) :
    rootAddresses (copy.roots roots) = (rootAddresses roots).image copy.address := by
  simp only [Mettapedia.Machines.ResourceOwnership.rootAddresses, Relocation.roots,
    Finset.image_image]
  rfl

omit [DecidableEq Address] in
theorem Relocation.allocated_iff {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (a : Address) :
    copy.address a ∈ destination.allocated ↔ a ∈ source.allocated := by
  rw [destination.allocated_iff, source.allocated_iff, copy.lookup_eq]
  cases found : source.lookup a with
  | none => simp
  | some cell => simp

omit [DecidableEq Address] in
theorem Relocation.valid_roots {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (valid : ValidRoots source roots) : ValidRoots destination (copy.roots roots) := by
  intro pair member
  obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
  exact (copy.allocated_iff original.2).mpr (valid original present)

omit [DecidableEq Address] in
/-- Copying cannot repair an invalid source root, even when the destination
contains additional allocations. -/
theorem Relocation.valid_roots_iff {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) :
    ValidRoots destination (copy.roots roots) ↔ ValidRoots source roots := by
  constructor
  · intro valid pair member
    apply (copy.allocated_iff pair.2).mp
    exact valid (pair.1, copy.address pair.2)
      (Finset.mem_image.mpr ⟨pair, member, rfl⟩)
  · exact copy.valid_roots roots

private theorem Relocation.root_forward {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) (a : Address)
    (root : (source.toStore roots).root a) :
    (destination.toStore (copy.roots roots)).root (copy.address a) := by
  refine ⟨(copy.allocated_iff a).mpr root.1, ?_⟩
  rw [copy.rootAddresses]
  exact Finset.mem_image.mpr ⟨a, root.2, rfl⟩

private theorem Relocation.root_reflect {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (a : DestinationAddress) (root : (destination.toStore (copy.roots roots)).root a) :
    ∃ original, (source.toStore roots).root original ∧ copy.address original = a := by
  have rooted := root.2
  rw [copy.rootAddresses] at rooted
  obtain ⟨original, present, same⟩ := Finset.mem_image.mp rooted
  exact ⟨original, ⟨(copy.allocated_iff original).mp (same ▸ root.1), present⟩, same⟩

private theorem Relocation.edge_forward {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) (a b : Address)
    (edge : (source.toStore roots).pointsTo a b) :
    (destination.toStore (copy.roots roots)).pointsTo (copy.address a) (copy.address b) := by
  obtain ⟨cell, found, reference⟩ := edge
  refine ⟨cell.relocate copy.address copy.payload, ?_, ?_⟩
  · rw [copy.lookup_eq, found]
    rfl
  · exact Finset.mem_image.mpr ⟨b, reference, rfl⟩

private theorem Relocation.edge_reflect {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (a : Address) (b : DestinationAddress)
    (edge : (destination.toStore (copy.roots roots)).pointsTo (copy.address a) b) :
    ∃ original, (source.toStore roots).pointsTo a original ∧ copy.address original = b := by
  obtain ⟨cell, found, reference⟩ := edge
  rw [copy.lookup_eq] at found
  cases originalFound : source.lookup a with
  | none => simp [originalFound] at found
  | some original =>
      have same : original.relocate copy.address copy.payload = cell :=
        Option.some.inj (by simpa only [originalFound, Option.map_some] using found)
      rw [← same] at reference
      obtain ⟨child, present, equal⟩ := Finset.mem_image.mp reference
      exact ⟨child, ⟨original, originalFound, present⟩, equal⟩

/-- Every destination-live resource comes from an actual source path. No
extra reachability is introduced by copying into a larger destination heap. -/
theorem Relocation.live_iff {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (a : DestinationAddress) :
    Live destination (copy.roots roots) a ↔
      ∃ original, Live source roots original ∧ copy.address original = a := by
  constructor
  · exact fun live => live.reflect copy.address (copy.root_reflect roots) (copy.edge_reflect roots)
  · rintro ⟨original, live, rfl⟩
    exact live.map copy.address (copy.root_forward roots) (copy.edge_forward roots)

theorem Relocation.footprint_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) :
    footprint destination (copy.roots roots) = (footprint source roots).image copy.address := by
  ext a
  rw [mem_footprint, copy.live_iff, Finset.mem_image]
  simp only [mem_footprint]

theorem Relocation.census_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (valid : ValidRoots source roots) :
    census destination (copy.roots roots) = (census source roots).image copy.address := by
  rw [census_eq_footprint _ _ (copy.valid_roots roots valid), census_eq_footprint _ _ valid,
    copy.footprint_eq]

/-- The executable capture check preserves acceptance and refusal through
complete cell relocation. Address injectivity reflects each captured start;
unrelated destination storage supplies no missing source dependency. This
transports retention, without issuing operation or registry authority. -/
theorem Relocation.retentionCheck_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (captured : List Address) :
    RequestBorrow.retentionCheck destination (copy.roots roots)
        (captured.map copy.address) =
      RequestBorrow.retentionCheck source roots captured := by
  rw [Bool.eq_iff_iff, RequestBorrow.retentionCheck_iff,
    RequestBorrow.retentionCheck_iff]
  constructor
  · rintro ⟨valid, retained⟩
    refine ⟨(copy.valid_roots_iff roots).mp valid, ?_⟩
    intro start member
    have moved := retained (copy.address start)
      (List.mem_map.mpr ⟨start, member, rfl⟩)
    obtain ⟨original, live, same⟩ := (copy.live_iff roots _).mp moved
    exact copy.injective same ▸ live
  · rintro ⟨valid, retained⟩
    refine ⟨copy.valid_roots roots valid, ?_⟩
    intro start member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact (copy.live_iff roots _).mpr ⟨original, retained original present, rfl⟩

/-- Path interpretation uses destination lookup, rather than continuing to
borrow cells from the source heap. Ordered reference paths remain ordered. -/
theorem Relocation.walk_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (a : Address) (path : List Address) :
    walk destination (copy.address a) (path.map copy.address) =
      (walk source a path).map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload) := by
  induction path generalizing a with
  | nil =>
      simp only [List.map_nil, walk, copy.lookup_eq, Option.map_map]
      rfl
  | cons b rest ih =>
      simp only [List.map_cons, walk, copy.lookup_eq]
      cases found : source.lookup a with
      | none => rfl
      | some cell =>
          simp only [Option.map_some, Option.bind_some, Cell.relocate]
          have membership : copy.address b ∈ cell.references.image copy.address ↔
              b ∈ cell.references := by
            constructor
            · intro member
              obtain ⟨original, present, equal⟩ := Finset.mem_image.mp member
              exact copy.injective equal ▸ present
            · intro member
              exact Finset.mem_image.mpr ⟨b, member, rfl⟩
          simp only [membership]
          by_cases present : b ∈ cell.references
          · simp only [if_pos present]
            exact ih b
          · simp only [if_neg present, Option.map_none]

/-- An injective copy preserves and reflects alias identity; equal payloads
at different addresses are not silently identified. -/
theorem Relocation.aliases_iff {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (a b : Address) (left right : List Address) :
    Aliases destination (copy.address a) (left.map copy.address)
      (copy.address b) (right.map copy.address) ↔ Aliases source a left b right := by
  have pathAddress (start : Address) (path : List Address) :
      (walk destination (copy.address start) (path.map copy.address)).map Prod.fst =
        ((walk source start path).map Prod.fst).map copy.address := by
    rw [copy.walk_eq]
    simp only [Option.map_map]
    rfl
  unfold Aliases
  rw [pathAddress, pathAddress]
  constructor
  · rintro ⟨endpoint, first, second⟩
    obtain ⟨original, originalFirst, same⟩ := Option.map_eq_some_iff.mp first
    obtain ⟨other, originalSecond, otherSame⟩ := Option.map_eq_some_iff.mp second
    have equal : other = original := copy.injective (otherSame.trans same.symm)
    exact ⟨original, originalFirst, equal ▸ originalSecond⟩
  · rintro ⟨endpoint, first, second⟩
    exact ⟨copy.address endpoint, by rw [first]; rfl, by rw [second]; rfl⟩

omit [DecidableEq Owner] in
/-- Relocating physical identities preserves their first-encounter order.
Equal payloads do not authorize collapsing different addresses. -/
theorem Relocation.first_seen_address_order {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (addresses : List Address) :
    (addresses.map copy.address).eraseDups = addresses.eraseDups.map copy.address :=
  Mettapedia.Algebra.OccurrenceIdentity.eraseDups_map_injective
    copy.address copy.injective addresses

omit [DecidableEq Owner] in
/-- A saved census charges its old prefix once and adds only addresses not
already encountered. Relocation does not reset or split that identity account. -/
theorem Relocation.first_seen_resumed_account {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (earlier pending : List Address) :
    ((earlier.map copy.address ++ pending.map copy.address).eraseDups).length =
      earlier.eraseDups.length + (pending.removeAll earlier).eraseDups.length :=
  Mettapedia.Algebra.OccurrenceIdentity.first_seen_resumed_account
    copy.address copy.injective earlier pending

/-- Collection in the destination still preserves every transferred live
path. Its reads no longer depend on the source's physical lifetime. -/
theorem Relocation.walk_collect_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (a : Address) (live : Live source roots a) (path : List Address) :
    walk (collect destination (copy.roots roots)) (copy.address a) (path.map copy.address) =
      (walk source a path).map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload) := by
  rw [walk_collect destination (copy.roots roots)
    ((copy.live_iff roots _).mpr ⟨a, live, rfl⟩)]
  exact copy.walk_eq a path

omit [DecidableEq Owner] in
theorem Relocation.observe_paths_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (paths : List (Address × List Address)) :
    RequestBorrow.observe destination (RequestBorrow.relocatePaths copy.address paths) =
      (RequestBorrow.observe source paths).map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := by
  simp only [RequestBorrow.observe, RequestBorrow.relocatePaths, List.map_map]
  apply List.map_congr_left
  intro query _
  exact copy.walk_eq query.1 query.2

/-- A checked complete capture may be copied and read from the collected
destination. The exact ordered readout is transported, including repeated
paths and failed reads; no subsequent source lookup is used. -/
theorem Relocation.retentionCheck_preserves_collected_paths
    {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (captured : List Address)
    (checked : RequestBorrow.retentionCheck source roots captured = true)
    (paths : List (Address × List Address))
    (covered : ∀ query ∈ paths, query.1 ∈ captured) :
    RequestBorrow.observe (collect destination (copy.roots roots))
        (RequestBorrow.relocatePaths copy.address paths) =
      (RequestBorrow.observe source paths).map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload)) := by
  have moved : RequestBorrow.retentionCheck destination (copy.roots roots)
      (captured.map copy.address) = true := by
    rw [copy.retentionCheck_eq roots captured]
    exact checked
  rw [RequestBorrow.retentionCheck_preserves_paths destination (copy.roots roots)
    (captured.map copy.address) moved _ (by
      intro query member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact List.mem_map.mpr ⟨original.1, covered original present, rfl⟩)]
  exact copy.observe_paths_eq paths

namespace RequestBorrow

/-- A relocated borrow is issued only after checking its source lifetime.
The destination region supplies the new lifetime; transporting paths does not
publish additional strong roots or extend either region's lifetime. -/
def transport (source : Region Owner Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address) :
    Option (View Owner DestinationAddress) :=
  view.transportIfCurrent source.stamp destination.stamp copy.address

omit [DecidableEq Address] in
theorem transport_eq_some_iff (source : Region Owner Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address)
    (moved : View Owner DestinationAddress) :
    transport source destination copy view = some moved ↔
      view.stamp = source.stamp ∧
        moved = ⟨destination.stamp, relocatePaths copy.address view.paths⟩ := by
  exact view.transportIfCurrent_eq_some_iff _ _ _ _

omit [DecidableEq Address] in
theorem transport_none_iff (source : Region Owner Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address) :
    transport source destination copy view = none ↔ view.stamp ≠ source.stamp := by
  exact view.transportIfCurrent_none_iff _ _ _

/-- The checker preserves complete ordered readouts, including failed paths
and repeated observations. A refused source borrow stays refused. -/
theorem transport_read_eq (source : Region Owner Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address) :
    (transport source destination copy view).bind (read destination) =
      (read source view).map (List.map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload))) := by
  by_cases issued : view.stamp = source.stamp
  · simp only [transport, View.transportIfCurrent, if_pos issued, Option.bind_some, read, ↓reduceIte,
      Option.map_some]
    congr 1
    exact copy.observe_paths_eq view.paths
  · simp only [transport, View.transportIfCurrent, Option.bind_none, read, if_neg issued,
      Option.map_none]

/-- Unchanged generations permit further immutable destination allocations.
The copied view continues reading destination storage, not the source graph. -/
theorem transport_read_history (source : Region Owner Address Value)
    (destination current : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address)
    (history : History destination current) (same : current.stamp = destination.stamp)
    (valid : ∀ query ∈ view.paths, query.1 ∈ source.heap.allocated) :
    (transport source destination copy view).bind (read current) =
      (read source view).map (List.map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload))) := by
  by_cases issued : view.stamp = source.stamp
  · simp only [transport, View.transportIfCurrent, if_pos issued, Option.bind_some]
    rw [read_exact history _ rfl same.symm]
    · simp only [read, if_pos issued, Option.map_some]
      congr 1
      exact copy.observe_paths_eq view.paths
    · intro query member
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact (copy.allocated_iff original.1).mpr (valid original present)
  · simp only [transport, View.transportIfCurrent, Option.bind_none, read, if_neg issued,
      Option.map_none]

omit [DecidableEq Address] in
/-- Address reuse after a reset does not turn a stale borrow into a newly
issued destination view, even if every old path has a copied image. -/
theorem transport_reset_rejected (source : Region Owner Address Value)
    (replacement : Heap Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation (reset source replacement).heap destination.heap)
    (view : View Owner Address) (issued : view.stamp = source.stamp) :
    transport (reset source replacement) destination copy view = none := by
  exact view.transportIfCurrent_reset_rejected source.stamp destination.stamp
    copy.address issued

omit [DecidableEq Address] in
theorem transport_foreign_rejected (source : Region Owner Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address)
    (different : view.stamp.identity ≠ source.stamp.identity) :
    transport source destination copy view = none := by
  exact view.transportIfCurrent_foreign_rejected source.stamp destination.stamp
    copy.address different

omit [DecidableEq Address] in
/-- A newly issued destination view still expires at a destination reset.
Copying its paths does not exempt it from the normal generation check. -/
theorem transport_destination_reset_rejected (source : Region Owner Address Value)
    (destination : Region Owner DestinationAddress DestinationValue)
    (replacement : Heap DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (view : View Owner Address) :
    (transport source destination copy view).bind (read (reset destination replacement)) =
      none := by
  by_cases issued : view.stamp = source.stamp
  · simp only [transport, View.transportIfCurrent, if_pos issued, Option.bind_some]
    exact read_reset_rejected _ _ _ rfl
  · simp only [transport, View.transportIfCurrent, if_neg issued, Option.bind_none]

end RequestBorrow

end Relocation

/-! ## Moving private addresses while retaining an external region

A live store may supply another row after a private continuation moves. Those
fresh rows retain their physical addresses. Relocating every cached operand to
fresh addresses preserves copied/copy aliases, but need not preserve comparison
with a fresh store row. A closed external region fixed by the common map avoids
that fracture. The store's lifetime, revision and occurrence pins remain duties
of the provider; a fixed address alone does not provide authority to read it.
-/

section FixedRegion

/-- Fixing a cell's value and every outgoing address retains the complete cell. -/
theorem Cell.relocate_eq_of_fixed (cell : Cell Address Value)
    (address : Address → Address) (payload : Value → Value)
    (fixed : ∀ a ∈ cell.references, address a = a) (valueFixed : payload cell.value = cell.value) :
    cell.relocate address payload = cell := by
  have refs : cell.references.image address = cell.references := by
    ext a
    constructor
    · intro member
      obtain ⟨original, present, same⟩ := Finset.mem_image.mp member
      exact (fixed original present).symm.trans same ▸ present
    · intro member
      exact Finset.mem_image.mpr ⟨a, member, fixed a member⟩
  change ⟨payload cell.value, cell.references.image address, cell.bytes⟩ = cell
  rw [valueFixed, refs]

/-- A checked map that fixes a reference-closed region retains every complete
lookup in that region, including absent entries. -/
theorem Relocation.lookup_fixed_region {source destination : Heap Address Value}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) {a : Address} (member : a ∈ region) :
    destination.lookup a = source.lookup a := by
  calc
    destination.lookup a = destination.lookup (copy.address a) :=
      congrArg destination.lookup (fixed a member).symm
    _ = (source.lookup a).map (Cell.relocate copy.address copy.payload) := copy.lookup_eq a
    _ = source.lookup a := by
      cases found : source.lookup a with
      | none => rfl
      | some cell =>
          rw [Option.map_some, cell.relocate_eq_of_fixed copy.address copy.payload]
          · intro next reference
            apply fixed next
            apply closed a member
            simpa only [Heap.dependencies, found, Option.map_some, Option.getD_some] using reference
          · exact values a member cell found

/-- All finite paths from a retained external root keep the original complete
observation. Failed paths are covered even when their requested address lies
outside the region. -/
theorem Relocation.walk_fixed_region {source destination : Heap Address Value}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) (path : List Address)
    {a : Address} (member : a ∈ region) : walk destination a path = walk source a path := by
  induction path generalizing a with
  | nil => simp only [walk, copy.lookup_fixed_region region closed fixed values member]
  | cons next rest ih =>
      simp only [walk, copy.lookup_fixed_region region closed fixed values member]
      cases found : source.lookup a with
      | none => rfl
      | some cell =>
          simp only [Option.bind_some]
          split
          next reference =>
            apply ih
            apply closed a member
            simpa only [Heap.dependencies, found, Option.map_some, Option.getD_some] using reference
          next _ => rfl

private theorem Relocation.fixed_region_output {source destination : Heap Address Value}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) (path : List Address)
    {a : Address} (member : a ∈ region) :
    (walk source a path).map (fun pair =>
      (copy.address pair.1, pair.2.relocate copy.address copy.payload)) = walk source a path := by
  cases found : walk source a path with
  | none => rfl
  | some pair =>
      have endpoint := walk_endpoint_in_closed source region closed path member found
      have cellFound := walk_success_lookup source path found
      simp only [Option.map_some]
      rw [fixed pair.1 endpoint, pair.2.relocate_eq_of_fixed copy.address copy.payload]
      · intro next reference
        apply fixed next
        apply closed pair.1 endpoint
        simpa only [Heap.dependencies, cellFound, Option.map_some, Option.getD_some] using reference
      · exact values pair.1 endpoint pair.2 cellFound

/-- A cached private path and a freshly obtained external path preserve and
reflect alias identity under the same checked map. Only the cached side is
relocated in the observation; the fresh external path is used as supplied. -/
theorem Relocation.mixed_aliases_iff {source destination : Heap Address Value}
    (copy : Relocation source destination) (region : Finset Address)
    (closed : ∀ a ∈ region, source.dependencies a ⊆ region)
    (fixed : ∀ a ∈ region, copy.address a = a)
    (values : ∀ a ∈ region, ∀ cell, source.lookup a = some cell →
      copy.payload cell.value = cell.value) (a b : Address) (left right : List Address)
    (externalRoot : b ∈ region) :
    Aliases destination (copy.address a) (left.map copy.address) b right ↔
      Aliases source a left b right := by
  have rightSame : walk destination (copy.address b) (right.map copy.address) =
      walk destination b right := by
    rw [copy.walk_eq,
      copy.fixed_region_output region closed fixed values right externalRoot,
      copy.walk_fixed_region region closed fixed values right externalRoot]
  have bothMoved := copy.aliases_iff a b left right
  unfold Aliases at bothMoved ⊢
  rw [rightSame] at bothMoved
  exact bothMoved

/-- Comparison of a relocated cached address with a retained physical address
is exact. Injectivity prevents private addresses from merging into that row. -/
theorem Relocation.eq_retained_address_iff {source destination : Heap Address Value}
    (copy : Relocation source destination) (cached external : Address)
    (fixed : copy.address external = external) :
    copy.address cached = external ↔ cached = external := by
  constructor
  · intro same
    exact copy.injective (same.trans fixed.symm)
  · rintro rfl
    exact fixed

end FixedRegion

/-! ## Owner lifecycle -/

variable [DecidableEq Owner]

def cancel (roots : Roots Owner Address) (dead : Finset Owner) : Roots Owner Address :=
  roots.filter (fun pair => pair.1 ∉ dead)

def release (roots : Roots Owner Address) (owner : Owner) : Roots Owner Address :=
  cancel roots {owner}

omit [DecidableEq Address] in
@[simp] theorem mem_cancel (roots : Roots Owner Address) (dead : Finset Owner)
    (pair : Owner × Address) :
    pair ∈ cancel roots dead ↔ pair ∈ roots ∧ pair.1 ∉ dead := by
  simp [cancel]

omit [DecidableEq Address] in
@[simp] theorem mem_release (roots : Roots Owner Address) (owner : Owner)
    (pair : Owner × Address) :
    pair ∈ release roots owner ↔ pair ∈ roots ∧ pair.1 ≠ owner := by
  simp [release]

theorem release_union (first second : Roots Owner Address) (owner : Owner) :
    release (first ∪ second) owner = release first owner ∪ release second owner := by
  ext pair
  simp only [mem_release, Finset.mem_union]
  tauto

@[simp] theorem release_snapshotRoots (heap : Heap Address Value) (owner : Owner) :
    release (heap.snapshotRoots owner) owner = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair member
  obtain ⟨captured, different⟩ := (mem_release _ _ _).mp member
  obtain ⟨address, _, rfl⟩ := Finset.mem_image.mp captured
  exact different rfl

/-- Closing a heap inspector removes its snapshot pin. Other owners' roots
remain governed by their existing release contract. -/
theorem release_inspection (heap : Heap Address Value) (roots : Roots Owner Address)
    (inspector : Owner) :
    release (roots ∪ heap.snapshotRoots inspector) inspector = release roots inspector := by
  rw [release_union, release_snapshotRoots, Finset.union_empty]

omit [DecidableEq Address] in
theorem cancel_subset (roots : Roots Owner Address) (dead : Finset Owner) :
    cancel roots dead ⊆ roots := Finset.filter_subset _ _

theorem live_cancel_mono (h : Heap Address Value) (roots : Roots Owner Address)
    (dead : Finset Owner) {a : Address} :
    Live h (cancel roots dead) a → Live h roots a :=
  live_mono h (cancel_subset roots dead)

/-- Cancelling more owners cannot create a newly live resource. -/
theorem live_cancel_antitone (h : Heap Address Value) (roots : Roots Owner Address)
    {dead moreDead : Finset Owner} (subset : dead ⊆ moreDead) {a : Address} :
    Live h (cancel roots moreDead) a → Live h (cancel roots dead) a := by
  apply live_mono h
  intro pair member
  obtain ⟨present, retained⟩ := (mem_cancel roots moreDead pair).mp member
  exact (mem_cancel roots dead pair).mpr ⟨present, fun gone => retained (subset gone)⟩

theorem footprint_cancel_subset (h : Heap Address Value) (roots : Roots Owner Address)
    (dead : Finset Owner) : footprint h (cancel roots dead) ⊆ footprint h roots :=
  footprint_mono h (cancel_subset roots dead)

theorem live_release_mono (h : Heap Address Value) (roots : Roots Owner Address)
    (owner : Owner) {a : Address} :
    Live h (release roots owner) a → Live h roots a :=
  live_cancel_mono h roots {owner}

/-- Cancelling every owner other than `survivor` retains the graph reachable
from that survivor's own roots. The opposite direction is `live_cancel_mono`:
cancellation does not make a new resource live. -/
theorem live_cancel_other_owner (heap : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (survivor : Owner)
    (outside : survivor ∉ dead) {address : Address}
    (live : Live heap (roots.filter fun pair => pair.1 = survivor) address) :
    Live heap (cancel roots dead) address := by
  refine live_mono heap ?_ live
  intro pair member
  obtain ⟨present, sameOwner⟩ := Finset.mem_filter.mp member
  refine (mem_cancel roots dead pair).mpr ⟨present, ?_⟩
  rw [sameOwner]
  exact outside

/-- Releasing one owner retains the graph rooted at a different owner. -/
theorem live_release_other_owner (heap : Heap Address Value)
    (roots : Roots Owner Address) (released survivor : Owner)
    (different : survivor ≠ released) {address : Address}
    (live : Live heap (roots.filter fun pair => pair.1 = survivor) address) :
    Live heap (release roots released) address := by
  refine live_cancel_other_owner heap roots {released} survivor ?_ live
  intro member
  exact different (Finset.mem_singleton.mp member)

/-- Reclamation after the final protecting owner disappears.  The hypothesis
accounts for *every transitive path*, including ones through sibling roots. -/
theorem final_owners_reclaimed (h : Heap Address Value)
    (roots : Roots Owner Address) (dead : Finset Owner) (a : Address)
    (lastOwners : ∀ pair ∈ roots, Live h {pair} a → pair.1 ∈ dead) :
    (collect h (cancel roots dead)).lookup a = none := by
  rw [lookup_collect_none_iff, live_iff_root]
  rintro ⟨pair, retained, live⟩
  obtain ⟨present, notDead⟩ := (mem_cancel roots dead pair).mp retained
  exact notDead (lastOwners pair present live)

def retag (source destination : Owner) (pair : Owner × Address) : Owner × Address :=
  (if pair.1 = source then destination else pair.1, pair.2)

/-- Ownership moves without copying or changing resource identity. -/
def transfer (roots : Roots Owner Address) (source destination : Owner) :
    Roots Owner Address := roots.image (retag source destination)

/-- A new owner shares the source owner's roots; existing owners keep theirs. -/
def fork (roots : Roots Owner Address) (source destination : Owner) :
    Roots Owner Address := roots ∪ transfer roots source destination

@[simp] theorem rootAddresses_transfer (roots : Roots Owner Address)
    (source destination : Owner) :
    rootAddresses (transfer roots source destination) = rootAddresses roots := by
  simp only [rootAddresses, transfer, Finset.image_image]
  rfl

@[simp] theorem rootAddresses_fork (roots : Roots Owner Address)
    (source destination : Owner) :
    rootAddresses (fork roots source destination) = rootAddresses roots := by
  simp only [fork, rootAddresses, Finset.image_union]
  change rootAddresses roots ∪ rootAddresses (transfer roots source destination) = _
  rw [rootAddresses_transfer, Finset.union_self]
  rfl

/-- Sharing an existing graph with any finite sequence of owners preserves
its root addresses, including when an owner is retained more than once. -/
theorem rootAddresses_fork_list (roots : Roots Owner Address)
    (source : Owner) (destinations : List Owner) :
    rootAddresses (destinations.foldl (fun retained next => fork retained source next) roots) =
      rootAddresses roots := by
  induction destinations generalizing roots with
  | nil => rfl
  | cons next rest ih =>
      rw [List.foldl_cons, ih, rootAddresses_fork]

theorem live_transfer_iff (h : Heap Address Value) (roots : Roots Owner Address)
    (source destination : Owner) (a : Address) :
    Live h (transfer roots source destination) a ↔ Live h roots a :=
  live_congr_rootAddresses h _ _ (rootAddresses_transfer roots source destination) a

theorem live_fork_iff (h : Heap Address Value) (roots : Roots Owner Address)
    (source destination : Owner) (a : Address) :
    Live h (fork roots source destination) a ↔ Live h roots a :=
  live_congr_rootAddresses h _ _ (rootAddresses_fork roots source destination) a

/-- Releasing the old owner after an exclusive transfer leaves every
transferred root intact. The owner identities must actually differ. -/
theorem release_transferred_source (roots : Roots Owner Address) (source destination : Owner)
    (different : destination ≠ source) (owned : ∀ pair ∈ roots, pair.1 = source) :
    release (transfer roots source destination) source = transfer roots source destination := by
  ext pair
  rw [show release (transfer roots source destination) source =
    cancel (transfer roots source destination) {source} from rfl, mem_cancel]
  constructor
  · exact And.left
  · intro member
    refine ⟨member, ?_⟩
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
    simp only [retag, owned original present, if_true, Finset.mem_singleton]
    exact different

/-! ## In-flight borrows with other owners still present -/

/-- A distinct temporary owner protects the source's roots even when the
source is retired during the call. Other owners need not belong to the source. -/
theorem rootAddresses_release_after_fork (roots : Roots Owner Address)
    (source borrower : Owner) (different : borrower ≠ source) :
    rootAddresses (release (fork roots source borrower) source) = rootAddresses roots := by
  ext address
  constructor
  · intro present
    obtain ⟨pair, retained, same⟩ := Finset.mem_image.mp present
    have inFork := (mem_release (fork roots source borrower) source pair).mp retained
    have presentFork : address ∈ rootAddresses (fork roots source borrower) :=
      Finset.mem_image.mpr ⟨pair, inFork.1, same⟩
    simpa only [rootAddresses_fork] using presentFork
  · intro present
    obtain ⟨pair, original, same⟩ := Finset.mem_image.mp present
    by_cases fromSource : pair.1 = source
    · refine Finset.mem_image.mpr ⟨retag source borrower pair, ?_, same⟩
      apply (mem_release (fork roots source borrower) source _).mpr
      refine ⟨Finset.mem_union_right roots (Finset.mem_image.mpr ⟨pair, original, rfl⟩), ?_⟩
      simpa only [retag, fromSource, if_true] using different
    · exact Finset.mem_image.mpr ⟨pair,
        (mem_release (fork roots source borrower) source pair).mpr
          ⟨Finset.mem_union_left _ original, fromSource⟩, same⟩

/-- Releasing a fresh temporary owner restores precisely the pre-call owners.
Freshness prevents accidentally dropping an older reader with the same label. -/
theorem release_fresh_fork (roots : Roots Owner Address) (source borrower : Owner)
    (fresh : ∀ pair ∈ roots, pair.1 ≠ borrower) :
    release (fork roots source borrower) borrower = roots := by
  ext pair
  constructor
  · intro retained
    obtain ⟨present, notBorrower⟩ :=
      (mem_release (fork roots source borrower) borrower pair).mp retained
    rcases Finset.mem_union.mp present with original | transferred
    · exact original
    · obtain ⟨original, member, same⟩ := Finset.mem_image.mp transferred
      by_cases fromSource : original.1 = source
      · have borrowerOwner : pair.1 = borrower := by
          rw [← same]
          simp only [retag, fromSource, if_true]
        exact False.elim (notBorrower borrowerOwner)
      · have originalIsPair : original = pair := by
          simpa only [retag, fromSource, if_false] using same
        exact originalIsPair ▸ member
  · intro original
    exact (mem_release (fork roots source borrower) borrower pair).mpr
      ⟨Finset.mem_union_left _ original, fresh pair original⟩

omit [DecidableEq Address] in
theorem release_comm (roots : Roots Owner Address) (first second : Owner) :
    release (release roots first) second = release (release roots second) first := by
  ext pair
  simp only [mem_release, and_left_comm, and_comm]

/-- A call ending after source retirement removes only its own temporary roots.
Unrelated readers survive, and the source's roots are not resurrected. -/
theorem release_borrow_after_source (roots : Roots Owner Address)
    (source borrower : Owner) (fresh : ∀ pair ∈ roots, pair.1 ≠ borrower) :
    release (release (fork roots source borrower) source) borrower = release roots source := by
  rw [release_comm, release_fresh_fork roots source borrower fresh]

/-- The temporary root preserves successful and failed path observations,
including identity-bearing cells, across source retirement and collection. -/
theorem walk_collect_borrow (heap : Heap Address Value) (roots : Roots Owner Address)
    (source borrower : Owner) (different : borrower ≠ source) {address : Address}
    (live : Live heap roots address) (path : List Address) :
    walk (collect heap (release (fork roots source borrower) source)) address path =
      walk heap address path := by
  apply walk_collect
  exact (live_congr_rootAddresses heap _ roots
    (rootAddresses_release_after_fork roots source borrower different) address).mpr live

/-- Returning preserves the ordered observation list, without identifying
equal occurrences merely because they read the same shared resource. -/
theorem observations_collect_borrow (heap : Heap Address Value)
    (roots : Roots Owner Address) (source borrower : Owner) (different : borrower ≠ source)
    (paths : List (Address × List Address)) (live : ∀ path ∈ paths, Live heap roots path.1) :
    RequestBorrow.observe (collect heap (release (fork roots source borrower) source)) paths =
      RequestBorrow.observe heap paths := by
  unfold RequestBorrow.observe
  apply List.map_congr_left
  intro path member
  exact walk_collect_borrow heap roots source borrower different (live path member) path.2

/-- A borrower reusing the retiring source's owner label provides no protection. -/
theorem same_owner_borrow_loses_root (heap : Heap Address Value) (owner : Owner)
    (address : Address) :
    (collect heap (release (fork {(owner, address)} owner owner) owner)).lookup address =
      none := by
  have gone : release (fork {(owner, address)} owner owner) owner = ∅ := by
    ext pair
    simp [release, cancel, fork, transfer, retag]
    intro same
    exact congrArg Prod.fst same
  rw [gone]
  exact lookup_collect_of_not_live heap ∅ (not_live_empty heap address)

namespace PinnedReset

/-- Pin the current generation for a reader, then detach it from its store.
The new store generation has its own roots; this function describes only the
retired generation whose last reader will release it. -/
def roots (old : Roots Owner Address) (store reader : Owner) : Roots Owner Address :=
  release (fork old store reader) store

/-- Detachment leaves the reader's full transitive graph reachable. -/
theorem live_after_detach (heap : Heap Address Value) (old : Roots Owner Address)
    (store reader : Owner) (different : reader ≠ store)
    (owned : ∀ pair ∈ old, pair.1 = store) {address : Address}
    (live : Live heap old address) : Live heap (roots old store reader) address := by
  apply live_mono heap (show transfer old store reader ⊆ roots old store reader from ?_)
    ((live_transfer_iff heap old store reader address).mpr live)
  intro pair present
  apply (mem_release (fork old store reader) store pair).mpr
  refine ⟨Finset.mem_union_right old present, ?_⟩
  obtain ⟨original, member, rfl⟩ := Finset.mem_image.mp present
  simp only [retag, owned original member, if_true]
  exact different

/-- Ordered repeated path observations survive logical reset and collection.
This includes failed paths and resource addresses, not just payload equality. -/
theorem observations_after_detach (heap : Heap Address Value) (old : Roots Owner Address)
    (store reader : Owner) (different : reader ≠ store)
    (owned : ∀ pair ∈ old, pair.1 = store) (paths : List (Address × List Address))
    (live : ∀ path ∈ paths, Live heap old path.1) :
    RequestBorrow.observe (collect heap (roots old store reader)) paths =
      RequestBorrow.observe heap paths := by
  unfold RequestBorrow.observe
  apply List.map_congr_left
  intro path member
  exact walk_collect heap _ (live_after_detach heap old store reader different owned
    (live path member)) path.2

/-- Cancelling the last pinned reader removes every retired-generation root.
Storage cannot be retained merely because the store handle still exists. -/
theorem last_reader_releases (old : Roots Owner Address) (store reader : Owner)
    (owned : ∀ pair ∈ old, pair.1 = store) :
    release (roots old store reader) reader = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro pair member
  obtain ⟨retained, notReader⟩ := (mem_release (roots old store reader) reader pair).mp member
  obtain ⟨present, notStore⟩ := (mem_release (fork old store reader) store pair).mp retained
  rcases Finset.mem_union.mp present with original | transferred
  · exact notStore (owned pair original)
  · obtain ⟨original, originalMember, rfl⟩ := Finset.mem_image.mp transferred
    simp only [retag, owned original originalMember, if_true] at notReader
    exact notReader rfl

/-- Actual cell reclamation follows the last-reader operation, including cells
reachable only through cycles in the retired generation. -/
theorem last_reader_reclaims (heap : Heap Address Value) (old : Roots Owner Address)
    (store reader : Owner) (owned : ∀ pair ∈ old, pair.1 = store) (address : Address) :
    (collect heap (release (roots old store reader) reader)).lookup address = none := by
  rw [last_reader_releases old store reader owned]
  exact lookup_collect_of_not_live heap ∅ (not_live_empty heap address)

/-- A pinned old heap can stay readable while the same view is refused by the
new live generation. Retention does not renew an observation's authority. -/
theorem reset_separates_lifetime_from_currency
    (region : RequestBorrow.Region Owner Address Value) (replacement : Heap Address Value)
    (old : Roots Owner Address) (reader : Owner)
    (different : reader ≠ region.stamp.identity)
    (owned : ∀ pair ∈ old, pair.1 = region.stamp.identity)
    (view : RequestBorrow.View Owner Address) (issued : view.stamp = region.stamp)
    (live : ∀ path ∈ view.paths, Live region.heap old path.1) :
    RequestBorrow.observe (collect region.heap (roots old region.stamp.identity reader))
        view.paths = RequestBorrow.observe region.heap view.paths ∧
      RequestBorrow.read (RequestBorrow.reset region replacement) view = none :=
  ⟨observations_after_detach region.heap old region.stamp.identity reader different owned
      view.paths live, RequestBorrow.read_reset_rejected region replacement view issued⟩

end PinnedReset

namespace AcquiredUse

/-! An enrolled resource separates handle currency from admitted uses.  Each
holder and use below is an exact issued identity, not a printed integer.  The
operations model the atomic registry boundary; they return an extracted
payload for finalization after that boundary.  Enclosing contexts, foreign
dependencies, memory ordering and the native realization remain separate
obligations.  In particular, a lifetime use does not authorize mutation.
-/

universe uHolder uUse uResource

variable {Holder : Type uHolder} {Use : Type uUse} {Resource : Type uResource}
variable [DecidableEq Holder] [DecidableEq Use]

inductive Mode where
  | lifetime
  | exclusive
  deriving DecidableEq, Repr

structure State (Holder : Type uHolder) (Use : Type uUse) (Resource : Type uResource) where
  current : Bool
  holders : Finset Holder
  uses : Finset Use
  exclusive : Option Use
  resource : Option Resource
  deriving DecidableEq

structure Result (Holder : Type uHolder) (Use : Type uUse) (Resource : Type uResource) where
  next : State Holder Use Resource
  retired : Option Resource
  deriving DecidableEq

/-- The retained payload exists exactly while its slot or an admitted use
needs it.  Exclusive admission is tied to one actual use receipt. -/
structure WellFormed (state : State Holder Use Resource) : Prop where
  retained : state.resource.isSome = true ↔ state.current = true ∨ state.uses.Nonempty
  exclusive_issued : ∀ use, state.exclusive = some use → use ∈ state.uses

def initial (holder : Holder) (resource : Resource) : State Holder Use Resource :=
  ⟨true, {holder}, ∅, none, some resource⟩

omit [DecidableEq Holder] [DecidableEq Use] in
theorem initial_wellFormed (holder : Holder) (resource : Resource) :
    WellFormed (initial (Use := Use) holder resource) := by
  constructor
  · simp [initial]
  · simp [initial]

/-- Extraction clears the payload before a finalizer can reenter. -/
def extract (state : State Holder Use Resource) : Result Holder Use Resource :=
  if state.current = false ∧ state.uses = ∅ then
    ⟨{ state with resource := none }, state.resource⟩
  else ⟨state, none⟩

def detach (state : State Holder Use Resource) : Result Holder Use Resource :=
  extract { state with current := false }

def copyHolder (source destination : Holder) (state : State Holder Use Resource) :
    Option (Result Holder Use Resource) :=
  if source ∈ state.holders ∧ destination ∉ state.holders then
    some ⟨{ state with holders := insert destination state.holders }, none⟩
  else none

def releaseHolder (holder : Holder) (state : State Holder Use Resource) :
    Option (Result Holder Use Resource) :=
  if holder ∈ state.holders then
    let next := { state with holders := state.holders.erase holder }
    some (if next.holders = ∅ then detach next else ⟨next, none⟩)
  else none

def acquire (limit : Nat) (mode : Mode) (holder : Holder) (use : Use)
    (state : State Holder Use Resource) : Option (Result Holder Use Resource) :=
  if state.current = true ∧ holder ∈ state.holders ∧ use ∉ state.uses ∧
      state.uses.card < limit ∧ (mode = .lifetime ∨ state.exclusive = none) then
    some ⟨{ state with
      uses := insert use state.uses
      exclusive := if mode = .exclusive then some use else state.exclusive }, none⟩
  else none

def releaseUse (use : Use) (state : State Holder Use Resource) :
    Option (Result Holder Use Resource) :=
  if use ∈ state.uses then
    some (extract { state with
      uses := state.uses.erase use
      exclusive := if state.exclusive = some use then none else state.exclusive })
  else none

def moveUse (source destination : Use) (state : State Holder Use Resource) :
    Option (Result Holder Use Resource) :=
  if source ∈ state.uses ∧ destination ∉ state.uses then
    some ⟨{ state with
      uses := insert destination (state.uses.erase source)
      exclusive := if state.exclusive = some source then some destination else state.exclusive },
      none⟩
  else none

/-- Relinquish an admitted exclusive claim while keeping its exact memory
receipt. A caller freezes its return before this atomic boundary. -/
def demoteUse (use : Use) (state : State Holder Use Resource) :
    Option (Result Holder Use Resource) :=
  if use ∈ state.uses ∧ state.exclusive = some use then
    some ⟨{ state with exclusive := none }, none⟩
  else none

/-- A held receipt may issue a bounded lifetime edge, including after logical
close. This does not acquire another operation or renew registry currency. -/
def forkLifetime (limit : Nat) (source destination : Use) (state : State Holder Use Resource) :
    Option (Result Holder Use Resource) :=
  if source ∈ state.uses ∧ destination ∉ state.uses ∧ state.uses.card < limit then
    some ⟨{ state with uses := insert destination state.uses }, none⟩
  else none

/-- Existing admitted work may hold a detached payload.  The result supplies
memory access only; mutation needs the distinct exclusive receipt. -/
def readUse (use : Use) (state : State Holder Use Resource) : Option Resource :=
  if use ∈ state.uses then state.resource else none

def mayMutate (use : Use) (state : State Holder Use Resource) : Prop :=
  use ∈ state.uses ∧ state.exclusive = some use

instance instDecidableMayMutate (use : Use) (state : State Holder Use Resource) :
    Decidable (mayMutate use state) :=
  inferInstanceAs (Decidable (use ∈ state.uses ∧ state.exclusive = some use))

/-- New operations require both a current slot and its exact owning holder. -/
def readHolder (holder : Holder) (state : State Holder Use Resource) : Option Resource :=
  if state.current = true ∧ holder ∈ state.holders then state.resource else none

section PayloadTransitions

universe uReply
variable {Reply : Type uReply}

/-- Advance the owned abstract payload under its current exclusive use.
The returned state is stored even when the reply denotes refusal or a fault.
Lifecycle operations retain or extract the payload; this separate computation
operation changes it. Native address replacement and transitive edge updates
require their own storage refinement. -/
def transitionCurrent (use : Use) (step : Resource → Reply × Resource)
    (state : State Holder Use Resource) : Option (Reply × State Holder Use Resource) :=
  if state.current = true ∧ mayMutate use state then
    state.resource.map fun resource =>
      let reached := step resource
      (reached.1, { state with resource := some reached.2 })
  else none

omit [DecidableEq Holder] in
theorem transitionCurrent_admitted (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply)
    (accepted : transitionCurrent use step before = some (reply, after)) :
    before.current = true ∧ mayMutate use before ∧
      ∃ resource, before.resource = some resource ∧ reply = (step resource).1 ∧
        after = { before with resource := some (step resource).2 } := by
  unfold transitionCurrent at accepted
  split at accepted
  · rename_i allowed
    obtain ⟨resource, held, same⟩ := Option.map_eq_some_iff.mp accepted
    cases same
    exact ⟨allowed.1, allowed.2, resource, held, rfl, rfl⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem transitionCurrent_metadata (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply)
    (accepted : transitionCurrent use step before = some (reply, after)) :
    after.current = before.current ∧ after.holders = before.holders ∧
      after.uses = before.uses ∧ after.exclusive = before.exclusive := by
  obtain ⟨_, _, _, _, _, rfl⟩ := transitionCurrent_admitted use step before after reply accepted
  exact ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq Holder] in
theorem transitionCurrent_wellFormed (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply) (valid : WellFormed before)
    (accepted : transitionCurrent use step before = some (reply, after)) : WellFormed after := by
  obtain ⟨_, allowed, _, _, _, rfl⟩ := transitionCurrent_admitted use step before after reply accepted
  exact ⟨⟨fun _ => Or.inr ⟨use, allowed.1⟩, fun _ => rfl⟩, valid.exclusive_issued⟩

omit [DecidableEq Holder] in
/-- The same issued use sees the actual reached payload. No new use or
operation authority is minted by storing a computation result. -/
theorem transitionCurrent_read (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply)
    (accepted : transitionCurrent use step before = some (reply, after)) :
    ∃ resource, readUse use before = some resource ∧
      readUse use after = some (step resource).2 ∧ reply = (step resource).1 ∧
      after.current = true ∧ mayMutate use after := by
  obtain ⟨current, allowed, resource, held, answer, rfl⟩ := transitionCurrent_admitted use step before after reply accepted
  exact ⟨resource, by simp [readUse, allowed.1, held], by simp [readUse, allowed.1], answer, current, allowed⟩

omit [DecidableEq Holder] in
theorem transitionCurrent_refused (use : Use) (step : Resource → Reply × Resource)
    (state : State Holder Use Resource) (denied : ¬ (state.current = true ∧ mayMutate use state)) :
    transitionCurrent use step state = none := by simp [transitionCurrent, denied]

theorem transitionCurrent_readHolder
    (use : Use) (step : Resource → Reply × Resource) (holder : Holder)
    (before after : State Holder Use Resource) (reply : Reply)
    (heldBy : holder ∈ before.holders)
    (accepted : transitionCurrent use step before = some (reply, after)) :
    ∃ resource, before.resource = some resource ∧
      readHolder holder after = some (step resource).2 := by
  obtain ⟨current, _, resource, held, _, rfl⟩ := transitionCurrent_admitted use step before after reply accepted
  exact ⟨resource, held, by simp [readHolder, current, heldBy]⟩

omit [DecidableEq Holder] in
/-- Eligible, well-formed ownership cannot lose a result after the abstract
step. Native allocation/queue refusal must be represented in that step's reply
and reached state, not silently discard an earned prefix. -/
theorem transitionCurrent_total (use : Use) (step : Resource → Reply × Resource)
    (state : State Holder Use Resource) (valid : WellFormed state)
    (current : state.current = true) (allowed : mayMutate use state) :
    ∃ reply next, transitionCurrent use step state = some (reply, next) := by
  have someResource := valid.retained.mpr (Or.inl current)
  obtain ⟨resource, held⟩ := Option.isSome_iff_exists.mp someResource
  exact ⟨(step resource).1, { state with resource := some (step resource).2 },
    by simp [transitionCurrent, current, allowed, held]⟩

omit [DecidableEq Holder] in
theorem transitionCurrent_identity (use : Use) (reply : Reply) (state : State Holder Use Resource) :
    transitionCurrent use (fun resource => (reply, resource)) state =
      if state.current = true ∧ mayMutate use state ∧ state.resource.isSome then some (reply, state) else none := by
  cases state with
  | mk current holders uses exclusive resource =>
      cases resource <;> simp [transitionCurrent]

omit [DecidableEq Holder] in
/-- Successive service steps use the reached payload, not a copied initial
packet. This is a state-composition law; external effects require their actual
step semantics and delivery contracts. -/
theorem transitionCurrent_comp {SecondReply : Type uReply}
    (use : Use) (first : Resource → Reply × Resource) (second : Resource → SecondReply × Resource)
    (state : State Holder Use Resource) :
    transitionCurrent use (fun resource =>
      let left := first resource
      let right := second left.2
      ((left.1, right.1), right.2)) state =
      (transitionCurrent use first state).bind fun left =>
        (transitionCurrent use second left.2).map fun right => ((left.1, right.1), right.2) := by
  unfold transitionCurrent
  split
  · rename_i allowed
    cases held : state.resource with
    | none => simp
    | some resource =>
        simp only [Option.map_some, Option.bind_some]
        have stillAllowed : ({ state with resource := some (first resource).2 }).current = true ∧
            mayMutate use { state with resource := some (first resource).2 } := allowed
        simp only [if_pos stillAllowed, Option.map_some]
  · rfl

namespace TransitionControls

def owner : State Nat Nat (Nat × List Nat) := ⟨true, {1}, {7}, some 7, some (0, [])⟩

/-- A paused/refused reply may still carry earned work which must survive. -/
def pausedStep (saved : Nat × List Nat) : Bool × (Nat × List Nat) :=
  (false, (saved.1 + 1, saved.2 ++ [42]))

omit [DecidableEq Holder] in
theorem refused_reply_keeps_reached_state :
    (transitionCurrent 7 pausedStep owner).map (fun result => (result.1, result.2.resource)) =
      some (false, some (1, [42])) := by decide +kernel

omit [DecidableEq Holder] in
theorem copied_use_observes_later_payload :
    ((transitionCurrent 7 pausedStep owner).bind fun first => transitionCurrent 7 pausedStep first.2).map
      (fun result => result.2.resource) = some (some (2, [42, 42])) := by decide +kernel

omit [DecidableEq Holder] in
theorem dead_unknown_and_lifetime_uses_cannot_step :
    transitionCurrent 8 pausedStep owner = none ∧
      transitionCurrent 7 pausedStep { owner with exclusive := none } = none ∧
      transitionCurrent 7 pausedStep { owner with current := false } = none := by decide +kernel

end TransitionControls

end PayloadTransitions

omit [DecidableEq Holder] in
theorem extract_current (state : State Holder Use Resource) :
    (extract state).next.current = state.current := by
  unfold extract
  split <;> rfl

omit [DecidableEq Holder] in
theorem extract_uses (state : State Holder Use Resource) :
    (extract state).next.uses = state.uses := by
  unfold extract
  split <;> rfl

omit [DecidableEq Holder] in
theorem extract_exclusive (state : State Holder Use Resource) :
    (extract state).next.exclusive = state.exclusive := by
  unfold extract
  split <;> rfl

omit [DecidableEq Holder] in
theorem extract_wellFormed (state : State Holder Use Resource)
    (retained : state.current = true ∨ state.uses.Nonempty → state.resource.isSome = true)
    (exclusive : ∀ use, state.exclusive = some use → use ∈ state.uses) :
    WellFormed (extract state).next := by
  unfold extract
  split
  · rename_i idle
    constructor
    · simp [idle.1, idle.2]
    · exact exclusive
  · rename_i busy
    have needed : state.current = true ∨ state.uses.Nonempty := by
      cases currency : state.current with
      | true => exact Or.inl rfl
      | false =>
        right
        apply Finset.nonempty_iff_ne_empty.mpr
        intro empty
        exact busy ⟨currency, empty⟩
    exact ⟨⟨fun _ => needed, fun _ => retained needed⟩, exclusive⟩

omit [DecidableEq Holder] in
theorem detach_wellFormed (state : State Holder Use Resource)
    (valid : WellFormed state) : WellFormed (detach state).next := by
  apply extract_wellFormed
  · rintro (openSlot | active)
    · cases openSlot
    · exact valid.retained.mpr (Or.inr active)
  · exact valid.exclusive_issued

omit [DecidableEq Holder] in
theorem detach_revokes (state : State Holder Use Resource) :
    (detach state).next.current = false := extract_current _

theorem detached_acquire_refused (limit : Nat) (mode : Mode) (holder : Holder)
    (use : Use) (state : State Holder Use Resource) :
    acquire limit mode holder use (detach state).next = none := by
  simp [acquire, detach_revokes]

theorem detached_holder_refused (holder : Holder) (state : State Holder Use Resource) :
    readHolder holder (detach state).next = none := by
  simp [readHolder, detach_revokes]

omit [DecidableEq Holder] in
/-- Detachment with an admitted use extracts no payload and preserves every
issued use, including its exclusive operation authorization. -/
theorem detach_with_use (state : State Holder Use Resource) {use : Use}
    (issued : use ∈ state.uses) :
    detach state = ⟨{ state with current := false }, none⟩ := by
  have nonempty : state.uses ≠ ∅ := Finset.ne_empty_of_mem issued
  simp [detach, extract, nonempty]

omit [DecidableEq Holder] in
theorem detached_read_preserved (state : State Holder Use Resource) {use : Use}
    (issued : use ∈ state.uses) :
    readUse use (detach state).next = state.resource := by
  rw [detach_with_use state issued]
  simp [readUse, issued]

omit [DecidableEq Holder] in
theorem detached_mutation_iff (state : State Holder Use Resource) (use : Use) :
    mayMutate use (detach state).next ↔ mayMutate use state := by
  simp only [mayMutate, detach, extract_uses, extract_exclusive]

omit [DecidableEq Holder] in
theorem unknown_use_refused (state : State Holder Use Resource) (use : Use)
    (unknown : use ∉ state.uses) : releaseUse use state = none ∧ readUse use state = none := by
  simp [releaseUse, readUse, unknown]

theorem wrong_holder_refused (limit : Nat) (mode : Mode) (state : State Holder Use Resource)
    (holder : Holder) (use : Use) (unknown : holder ∉ state.holders) :
    acquire limit mode holder use state = none := by
  simp [acquire, unknown]

theorem full_use_count_refused (limit : Nat) (mode : Mode) (state : State Holder Use Resource)
    (holder : Holder) (use : Use) (full : limit ≤ state.uses.card) :
    acquire limit mode holder use state = none := by
  simp [acquire, Nat.not_lt.mpr full]

theorem exclusive_competitor_refused (limit : Nat) (state : State Holder Use Resource)
    (holder : Holder) (use active : Use) (exclusive : state.exclusive = some active) :
    acquire limit .exclusive holder use state = none := by
  simp [acquire, exclusive]

omit [DecidableEq Holder] [DecidableEq Use] in
theorem mutation_unique (state : State Holder Use Resource) {left right : Use}
    (first : mayMutate left state) (second : mayMutate right state) : left = right := by
  exact Option.some.inj (first.2.symm.trans second.2)

theorem acquire_wellFormed (limit : Nat) (mode : Mode) (holder : Holder) (use : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : acquire limit mode holder use state = some result) :
    WellFormed result.next := by
  unfold acquire at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    constructor
    · exact ⟨fun _ => Or.inl admitted.1, fun _ => valid.retained.mpr (Or.inl admitted.1)⟩
    · intro other exclusive
      by_cases modeExclusive : mode = .exclusive
      · simp only [modeExclusive, if_true] at exclusive
        cases Option.some.inj exclusive
        exact Finset.mem_insert_self _ _
      · simp only [modeExclusive, if_false] at exclusive
        exact Finset.mem_insert_of_mem (valid.exclusive_issued other exclusive)
  · cases accepted

theorem acquire_count (limit : Nat) (mode : Mode) (holder : Holder) (use : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : acquire limit mode holder use state = some result) :
    result.next.uses.card = state.uses.card + 1 ∧ result.next.uses.card ≤ limit := by
  unfold acquire at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    constructor
    · exact Finset.card_insert_of_notMem admitted.2.2.1
    · calc
        (insert use state.uses).card = state.uses.card + 1 :=
          Finset.card_insert_of_notMem admitted.2.2.1
        _ ≤ limit := Nat.succ_le_of_lt admitted.2.2.2.1
  · cases accepted

omit [DecidableEq Holder] in
theorem releaseUse_wellFormed (use : Use) {state : State Holder Use Resource}
    {result : Result Holder Use Resource} (valid : WellFormed state)
    (accepted : releaseUse use state = some result) : WellFormed result.next := by
  unfold releaseUse at accepted
  split at accepted
  · rename_i issued
    cases Option.some.inj accepted
    apply extract_wellFormed
    · rintro (openSlot | active)
      · exact valid.retained.mpr (Or.inl openSlot)
      · obtain ⟨other, present⟩ := active
        exact valid.retained.mpr (Or.inr ⟨other, (Finset.mem_erase.mp present).2⟩)
    · intro other exclusive
      by_cases held : state.exclusive = some use
      · simp [held] at exclusive
      · simp only [held, if_false] at exclusive
        apply Finset.mem_erase.mpr
        refine ⟨?_, valid.exclusive_issued other exclusive⟩
        intro same
        apply held
        simpa [same] using exclusive
  · cases accepted

omit [DecidableEq Holder] in
theorem releaseUse_count (use : Use) {state : State Holder Use Resource}
    {result : Result Holder Use Resource} (accepted : releaseUse use state = some result) :
    result.next.uses.card = state.uses.card - 1 := by
  unfold releaseUse at accepted
  split at accepted
  · rename_i issued
    cases Option.some.inj accepted
    rw [extract_uses, Finset.card_erase_of_mem issued]
  · cases accepted

omit [DecidableEq Holder] in
theorem last_use_extracts (state : State Holder Use Resource) (use : Use)
    (valid : WellFormed state) (closed : state.current = false) (last : state.uses = {use}) :
    releaseUse use state = some ⟨{ state with uses := ∅, exclusive := none, resource := none },
      state.resource⟩ := by
  have exclusive : state.exclusive = some use ∨ state.exclusive = none := by
    cases held : state.exclusive with
    | none => exact Or.inr rfl
    | some other =>
      have issued := valid.exclusive_issued other held
      rw [last, Finset.mem_singleton] at issued
      exact Or.inl (congrArg some issued)
  rcases exclusive with held | empty
  · simp [releaseUse, extract, closed, last, held]
  · simp [releaseUse, extract, closed, last, empty]

omit [DecidableEq Use] in
theorem copyHolder_wellFormed (source destination : Holder)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : copyHolder source destination state = some result) :
    WellFormed result.next := by
  unfold copyHolder at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ⟨valid.retained, valid.exclusive_issued⟩
  · cases accepted

theorem releaseHolder_wellFormed (holder : Holder)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : releaseHolder holder state = some result) :
    WellFormed result.next := by
  unfold releaseHolder at accepted
  split at accepted
  · dsimp only at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact detach_wellFormed _ ⟨valid.retained, valid.exclusive_issued⟩
    · cases Option.some.inj accepted
      exact ⟨valid.retained, valid.exclusive_issued⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem moveUse_wellFormed (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : moveUse source destination state = some result) :
    WellFormed result.next := by
  unfold moveUse at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    constructor
    · exact ⟨fun _ => Or.inr ⟨destination, Finset.mem_insert_self _ _⟩,
        fun _ => valid.retained.mpr (Or.inr ⟨source, admitted.1⟩)⟩
    · intro other exclusive
      by_cases held : state.exclusive = some source
      · simp only [held, if_true] at exclusive
        cases Option.some.inj exclusive
        exact Finset.mem_insert_self _ _
      · simp only [held, if_false] at exclusive
        apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨?_, valid.exclusive_issued other exclusive⟩
        intro same
        apply held
        simpa [same] using exclusive
  · cases accepted

omit [DecidableEq Holder] in
theorem moveUse_count (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : moveUse source destination state = some result) :
    result.next.uses.card = state.uses.card := by
  unfold moveUse at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    have fresh : destination ∉ state.uses.erase source := by
      intro present
      exact admitted.2 (Finset.mem_erase.mp present).2
    change (insert destination (state.uses.erase source)).card = state.uses.card
    rw [Finset.card_insert_of_notMem fresh, Finset.card_erase_of_mem admitted.1]
    have positive : 0 < state.uses.card := Finset.card_pos.mpr ⟨source, admitted.1⟩
    omega
  · cases accepted

omit [DecidableEq Holder] in
theorem moveUse_keeps_currency (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : moveUse source destination state = some result) :
    result.next.current = state.current ∧ result.next.resource = state.resource := by
  unfold moveUse at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ⟨rfl, rfl⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem demoteUse_wellFormed (use : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : demoteUse use state = some result) :
    WellFormed result.next := by
  unfold demoteUse at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ⟨valid.retained, by simp⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem demoteUse_keeps_memory (use : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : demoteUse use state = some result) :
    result.next.current = state.current ∧ result.next.resource = state.resource ∧
      result.next.uses = state.uses ∧ result.retired = none := by
  unfold demoteUse at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem demoteUse_removes_mutation (use : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : demoteUse use state = some result) (other : Use) :
    ¬ mayMutate other result.next := by
  unfold demoteUse at accepted
  split at accepted
  · cases Option.some.inj accepted
    simp [mayMutate]
  · cases accepted

omit [DecidableEq Holder] in
theorem demoteUse_nonexclusive_refused (use : Use) (state : State Holder Use Resource)
    (unlicensed : state.exclusive ≠ some use) : demoteUse use state = none := by
  simp [demoteUse, unlicensed]

omit [DecidableEq Holder] in
theorem demoteUse_read_preserved (use other : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : demoteUse use state = some result) :
    readUse other result.next = readUse other state := by
  obtain ⟨_, resource, uses, _⟩ := demoteUse_keeps_memory use accepted
  simp only [readUse, uses, resource]

theorem demoteUse_permits_next_exclusive (limit : Nat) (use other : Use) (holder : Holder)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : demoteUse use state = some result) (current : state.current = true)
    (owned : holder ∈ state.holders) (fresh : other ∉ state.uses) (capacity : state.uses.card < limit) :
    acquire limit .exclusive holder other result.next =
      some ⟨{ result.next with
        uses := insert other result.next.uses,
        exclusive := some other }, none⟩ := by
  unfold demoteUse at accepted
  split at accepted
  · cases Option.some.inj accepted
    simp [acquire, current, owned, fresh, capacity]
  · cases accepted

omit [DecidableEq Holder] in
theorem forkLifetime_wellFormed (limit : Nat) (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : forkLifetime limit source destination state = some result) :
    WellFormed result.next := by
  unfold forkLifetime at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    constructor
    · exact ⟨fun _ => Or.inr (Finset.insert_nonempty _ _),
        fun _ => valid.retained.mpr (Or.inr ⟨source, admitted.1⟩)⟩
    · intro other exclusive
      exact Finset.mem_insert_of_mem (valid.exclusive_issued other exclusive)
  · cases accepted

omit [DecidableEq Holder] in
theorem forkLifetime_count (limit : Nat) (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result) :
    result.next.uses.card = state.uses.card + 1 ∧ result.next.uses.card ≤ limit := by
  unfold forkLifetime at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    change (insert destination state.uses).card = state.uses.card + 1 ∧
      (insert destination state.uses).card ≤ limit
    rw [Finset.card_insert_of_notMem admitted.2.1]
    exact ⟨rfl, Nat.succ_le_of_lt admitted.2.2⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem forkLifetime_keeps_currency (limit : Nat) (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result) :
    result.next.current = state.current ∧ result.next.resource = state.resource ∧
      result.next.exclusive = state.exclusive ∧ result.retired = none := by
  unfold forkLifetime at accepted
  split at accepted
  · cases Option.some.inj accepted
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases accepted

omit [DecidableEq Holder] in
theorem forkLifetime_same_payload (limit : Nat) (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result) :
    readUse destination result.next = readUse source state := by
  unfold forkLifetime at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    simp [readUse, admitted.1]
  · cases accepted

omit [DecidableEq Holder] in
theorem forkLifetime_lifetime_only (limit : Nat) (source destination : Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : forkLifetime limit source destination state = some result) :
    ¬ mayMutate destination result.next := by
  unfold forkLifetime at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    intro permission
    exact admitted.2.1 (valid.exclusive_issued destination permission.2)
  · cases accepted

theorem forkLifetime_closed_refuses_admission (limit : Nat) (source destination other : Use)
    (mode : Mode) (holder : Holder)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result)
    (closed : state.current = false) :
    readHolder holder result.next = none ∧
      acquire limit mode holder other result.next = none := by
  have currency := (forkLifetime_keeps_currency limit source destination accepted).1.trans closed
  simp [readHolder, acquire, currency]

omit [DecidableEq Holder] in
theorem forkLifetime_unknown_source_refused (limit : Nat) (source destination : Use)
    (state : State Holder Use Resource) (unknown : source ∉ state.uses) :
    forkLifetime limit source destination state = none := by
  simp [forkLifetime, unknown]

omit [DecidableEq Holder] in
theorem forkLifetime_nonempty_destination_refused (limit : Nat) (source destination : Use)
    (state : State Holder Use Resource) (occupied : destination ∈ state.uses) :
    forkLifetime limit source destination state = none := by
  simp [forkLifetime, occupied]

omit [DecidableEq Holder] in
theorem forkLifetime_full_count_refused (limit : Nat) (source destination : Use)
    (state : State Holder Use Resource) (full : limit ≤ state.uses.card) :
    forkLifetime limit source destination state = none := by
  simp [forkLifetime, Nat.not_lt.mpr full]

theorem last_holder_keeps_use (state : State Holder Use Resource) (holder : Holder)
    (use : Use) (last : state.holders = {holder}) (issued : use ∈ state.uses) :
    releaseHolder holder state =
      some ⟨{ state with current := false, holders := ∅ }, none⟩ := by
  have nonempty : state.uses ≠ ∅ := Finset.ne_empty_of_mem issued
  simp [releaseHolder, last, detach, extract, nonempty]

inductive Action (Holder : Type uHolder) (Use : Type uUse) where
  | copyHolder (source destination : Holder)
  | releaseHolder (holder : Holder)
  | acquire (mode : Mode) (holder : Holder) (use : Use)
  | releaseUse (use : Use)
  | moveUse (source destination : Use)
  | demoteUse (use : Use)
  | forkLifetime (source destination : Use)
  | close
  deriving DecidableEq, Repr

def step (limit : Nat) (state : State Holder Use Resource) :
    Action Holder Use → Option (Result Holder Use Resource)
  | .copyHolder source destination => copyHolder source destination state
  | .releaseHolder holder => releaseHolder holder state
  | .acquire mode holder use => acquire limit mode holder use state
  | .releaseUse use => releaseUse use state
  | .moveUse source destination => moveUse source destination state
  | .demoteUse use => demoteUse use state
  | .forkLifetime source destination => forkLifetime limit source destination state
  | .close => if state.current = true then some (detach state) else none

theorem step_wellFormed (limit : Nat) (action : Action Holder Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (valid : WellFormed state) (accepted : step limit state action = some result) :
    WellFormed result.next := by
  cases action with
  | copyHolder source destination => exact copyHolder_wellFormed source destination valid accepted
  | releaseHolder holder => exact releaseHolder_wellFormed holder valid accepted
  | acquire mode holder use => exact acquire_wellFormed limit mode holder use valid accepted
  | releaseUse use => exact releaseUse_wellFormed use valid accepted
  | moveUse source destination => exact moveUse_wellFormed source destination valid accepted
  | demoteUse use => exact demoteUse_wellFormed use valid accepted
  | forkLifetime source destination => exact forkLifetime_wellFormed limit source destination valid accepted
  | close =>
    simp only [step] at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact detach_wellFormed state valid
    · cases accepted

/-- Each operation either retains the same payload or extracts it once.
No transition constructs a replacement payload or revives a closed owner. -/
def ResourceTransition (state : State Holder Use Resource) (result : Result Holder Use Resource) :
    Prop :=
  (result.next.resource = state.resource ∧ result.retired = none) ∨
    (result.next.resource = none ∧ result.retired = state.resource)

omit [DecidableEq Holder] in
theorem extract_resourceTransition (state : State Holder Use Resource) :
    ResourceTransition state (extract state) := by
  unfold extract
  split
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

theorem step_resourceTransition (limit : Nat) (action : Action Holder Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : step limit state action = some result) : ResourceTransition state result := by
  cases action with
  | copyHolder source destination =>
    change copyHolder source destination state = some result at accepted
    unfold copyHolder at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inl ⟨rfl, rfl⟩
    · cases accepted
  | releaseHolder holder =>
    change releaseHolder holder state = some result at accepted
    unfold releaseHolder at accepted
    split at accepted
    · dsimp only at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact extract_resourceTransition _
      · cases Option.some.inj accepted
        exact Or.inl ⟨rfl, rfl⟩
    · cases accepted
  | acquire mode holder use =>
    change acquire limit mode holder use state = some result at accepted
    unfold acquire at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inl ⟨rfl, rfl⟩
    · cases accepted
  | releaseUse use =>
    change releaseUse use state = some result at accepted
    unfold releaseUse at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact extract_resourceTransition _
    · cases accepted
  | moveUse source destination =>
    change moveUse source destination state = some result at accepted
    unfold moveUse at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inl ⟨rfl, rfl⟩
    · cases accepted
  | demoteUse use =>
    change demoteUse use state = some result at accepted
    obtain ⟨_, resource, _, retired⟩ := demoteUse_keeps_memory use accepted
    exact Or.inl ⟨resource, retired⟩
  | forkLifetime source destination =>
    change forkLifetime limit source destination state = some result at accepted
    obtain ⟨_, resource, _, retired⟩ := forkLifetime_keeps_currency limit source destination accepted
    exact Or.inl ⟨resource, retired⟩
  | close =>
    simp only [step] at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact extract_resourceTransition _
    · cases accepted

theorem extracted_resource_absent (limit : Nat) (action : Action Holder Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource} {payload : Resource}
    (accepted : step limit state action = some result) (extracted : result.retired = some payload) :
    state.resource = some payload ∧ result.next.resource = none := by
  rcases step_resourceTransition limit action accepted with kept | retired
  · simp [kept.2] at extracted
  · exact ⟨retired.2.symm.trans extracted, retired.1⟩

theorem absent_resource_preserved (limit : Nat) (action : Action Holder Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (absent : state.resource = none) (accepted : step limit state action = some result) :
    result.next.resource = none ∧ result.retired = none := by
  rcases step_resourceTransition limit action accepted with kept | retired
  · exact ⟨kept.1.trans absent, kept.2⟩
  · exact ⟨retired.1, retired.2.trans absent⟩

theorem step_currency (limit : Nat) (action : Action Holder Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : step limit state action = some result) :
    result.next.current = state.current ∨ result.next.current = false := by
  cases action with
  | copyHolder source destination =>
    change copyHolder source destination state = some result at accepted
    unfold copyHolder at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inl rfl
    · cases accepted
  | releaseHolder holder =>
    change releaseHolder holder state = some result at accepted
    unfold releaseHolder at accepted
    split at accepted
    · dsimp only at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact Or.inr (detach_revokes _)
      · cases Option.some.inj accepted
        exact Or.inl rfl
    · cases accepted
  | acquire mode holder use =>
    change acquire limit mode holder use state = some result at accepted
    unfold acquire at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inl rfl
    · cases accepted
  | releaseUse use =>
    change releaseUse use state = some result at accepted
    unfold releaseUse at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inl (extract_current _)
    · cases accepted
  | moveUse source destination =>
    change moveUse source destination state = some result at accepted
    exact Or.inl (moveUse_keeps_currency source destination accepted).1
  | demoteUse use =>
    change demoteUse use state = some result at accepted
    exact Or.inl (demoteUse_keeps_memory use accepted).1
  | forkLifetime source destination =>
    change forkLifetime limit source destination state = some result at accepted
    exact Or.inl (forkLifetime_keeps_currency limit source destination accepted).1
  | close =>
    simp only [step] at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact Or.inr (detach_revokes _)
    · cases accepted

theorem step_closed (limit : Nat) (action : Action Holder Use)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (closed : state.current = false) (accepted : step limit state action = some result) :
    result.next.current = false := by
  rcases step_currency limit action accepted with same | revoked
  · exact same.trans closed
  · exact revoked

/-- A refused request keeps the complete unaccepted suffix.  The count is
accepted registry transitions, separate from provider work and elapsed cost. -/
structure Execution (Holder : Type uHolder) (Use : Type uUse) (Resource : Type uResource) where
  final : State Holder Use Resource
  retired : List Resource
  remaining : List (Action Holder Use)
  accepted : Nat

def run (limit : Nat) (state : State Holder Use Resource) :
    List (Action Holder Use) → Execution Holder Use Resource
  | [] => ⟨state, [], [], 0⟩
  | action :: tail =>
    match step limit state action with
    | none => ⟨state, [], action :: tail, 0⟩
    | some result =>
      let rest := run limit result.next tail
      ⟨rest.final, result.retired.toList ++ rest.retired, rest.remaining, rest.accepted + 1⟩

theorem run_wellFormed (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) (valid : WellFormed state) :
    WellFormed (run limit state actions).final := by
  induction actions generalizing state with
  | nil => exact valid
  | cons action tail ih =>
    cases accepted : step limit state action with
    | none => simpa only [run, accepted] using valid
    | some result =>
      simpa only [run, accepted] using
        ih result.next (step_wellFormed limit action valid accepted)

theorem run_absent (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) (absent : state.resource = none) :
    (run limit state actions).final.resource = none ∧
      (run limit state actions).retired = [] := by
  induction actions generalizing state with
  | nil => exact ⟨absent, rfl⟩
  | cons action tail ih =>
    cases accepted : step limit state action with
    | none => simpa only [run, accepted] using And.intro absent (rfl : ([] : List Resource) = [])
    | some result =>
      obtain ⟨nextAbsent, noExtraction⟩ := absent_resource_preserved limit action absent accepted
      obtain ⟨finalAbsent, noLaterExtraction⟩ := ih result.next nextAbsent
      simpa only [run, accepted, noExtraction, Option.toList_none, List.nil_append] using
        And.intro finalAbsent noLaterExtraction

/-- Extraction is exact across a finite accepted prefix, including a run
stopped by refusal. A later action cannot extract or replace that payload. -/
theorem run_resource (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) :
    ((run limit state actions).final.resource = state.resource ∧
      (run limit state actions).retired = []) ∨
    ((run limit state actions).final.resource = none ∧
      (run limit state actions).retired = state.resource.toList) := by
  induction actions generalizing state with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons action tail ih =>
    cases accepted : step limit state action with
    | none => simp [run, accepted]
    | some result =>
      rcases step_resourceTransition limit action accepted with kept | extracted
      · rcases ih result.next with laterKept | laterExtracted
        · left
          simp only [run, accepted, kept.2, Option.toList_none, List.nil_append]
          exact ⟨laterKept.1.trans kept.1, laterKept.2⟩
        · right
          simp only [run, accepted, kept.2, Option.toList_none, List.nil_append]
          exact ⟨laterExtracted.1, laterExtracted.2.trans (congrArg Option.toList kept.1)⟩
      · obtain ⟨finalAbsent, noLaterExtraction⟩ := run_absent limit tail result.next extracted.1
        right
        simp only [run, accepted, extracted.2, noLaterExtraction, List.append_nil]
        exact ⟨finalAbsent, trivial⟩

theorem run_extracts_at_most_once (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) : (run limit state actions).retired.length ≤ 1 := by
  rcases run_resource limit actions state with kept | extracted
  · simp [kept.2]
  · rw [extracted.2]
    cases state.resource <;> simp

theorem run_closed (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) (closed : state.current = false) :
    (run limit state actions).final.current = false := by
  induction actions generalizing state with
  | nil => exact closed
  | cons action tail ih =>
    cases accepted : step limit state action with
    | none => simpa only [run, accepted] using closed
    | some result =>
      simpa only [run, accepted] using ih result.next (step_closed limit action closed accepted)

theorem run_complete_residual (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) :
    (run limit state actions).remaining = actions.drop (run limit state actions).accepted ∧
      (run limit state actions).accepted ≤ actions.length := by
  induction actions generalizing state with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons action tail ih =>
    cases accepted : step limit state action with
    | none => simp [run, accepted]
    | some result =>
      obtain ⟨suffix, count⟩ := ih result.next
      simp only [run, accepted, List.drop_succ_cons, List.length_cons]
      exact ⟨suffix, Nat.add_le_add_right count 1⟩

theorem run_stopped_at_refusal (limit : Nat) (actions : List (Action Holder Use))
    (state : State Holder Use Resource) (action : Action Holder Use) (tail : List (Action Holder Use))
    (stopped : (run limit state actions).remaining = action :: tail) :
    step limit (run limit state actions).final action = none := by
  induction actions generalizing state with
  | nil => cases stopped
  | cons first rest ih =>
    cases accepted : step limit state first with
    | none =>
      simp only [run, accepted, List.cons.injEq] at stopped
      have refused : step limit state action = none := stopped.1 ▸ accepted
      simpa only [run, accepted] using refused
    | some result =>
      have suffix : (run limit result.next rest).remaining = action :: tail := by
        simpa only [run, accepted] using stopped
      simpa only [run, accepted] using ih result.next suffix

/-- The registry slot and each admitted use are distinct strong edges to the
same payload graph. Holder aliases do not give a closed slot a new edge. -/
def roots (state : State Holder Use Resource) (address : Resource → Address) :
    Roots (Unit ⊕ Use) Address :=
  match state.resource with
  | none => ∅
  | some payload =>
    (if state.current = true then {(Sum.inl (), address payload)} else ∅) ∪
      state.uses.image (fun use => (Sum.inr use, address payload))

omit [DecidableEq Holder] in
theorem use_rooted (state : State Holder Use Resource) (address : Resource → Address)
    {payload : Resource} {use : Use} (retained : state.resource = some payload)
    (issued : use ∈ state.uses) : (Sum.inr use, address payload) ∈ roots state address := by
  simp only [roots, retained]
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨use, issued, rfl⟩

omit [DecidableEq Holder] in
theorem rooted_address (state : State Holder Use Resource) (address : Resource → Address)
    {payload : Resource} (retained : state.resource = some payload)
    {pair : (Unit ⊕ Use) × Address} (present : pair ∈ roots state address) :
    pair.2 = address payload := by
  simp only [roots, retained, Finset.mem_union] at present
  rcases present with slot | use
  · split at slot
    · exact congrArg Prod.snd (Finset.mem_singleton.mp slot)
    · simp at slot
  · obtain ⟨use, _, rfl⟩ := Finset.mem_image.mp use
    rfl

omit [DecidableEq Holder] in
theorem rootAddresses_of_use (state : State Holder Use Resource) (address : Resource → Address)
    {payload : Resource} {use : Use} (retained : state.resource = some payload)
    (issued : use ∈ state.uses) : rootAddresses (roots state address) = {address payload} := by
  ext location
  constructor
  · intro member
    obtain ⟨pair, present, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_singleton.mpr (rooted_address state address retained present)
  · intro member
    rw [Finset.mem_singleton] at member
    subst location
    exact Finset.mem_image.mpr ⟨(Sum.inr use, address payload),
      use_rooted state address retained issued, rfl⟩

omit [DecidableEq Holder] in
theorem validRoots (state : State Holder Use Resource) (address : Resource → Address)
    (heap : Heap Address Value) {payload : Resource} (retained : state.resource = some payload)
    (allocated : address payload ∈ heap.allocated) : ValidRoots heap (roots state address) := by
  intro pair present
  rw [rooted_address state address retained present]
  exact allocated

omit [DecidableEq Holder] in
theorem demoteUse_keeps_roots (use : Use) (address : Resource → Address)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : demoteUse use state = some result) :
    roots result.next address = roots state address := by
  obtain ⟨currency, payload, uses, _⟩ := demoteUse_keeps_memory use accepted
  simp only [roots, currency, payload, uses]

omit [DecidableEq Holder] in
theorem forkLifetime_keeps_rootAddresses (limit : Nat) (source destination : Use)
    (address : Resource → Address)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result) :
    rootAddresses (roots result.next address) = rootAddresses (roots state address) := by
  unfold forkLifetime at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    cases retained : state.resource with
    | none => simp [roots, retained]
    | some payload =>
      rw [rootAddresses_of_use state address retained admitted.1]
      exact rootAddresses_of_use { state with
        resource := some payload,
        uses := insert destination state.uses } address rfl (Finset.mem_insert_self _ _)
  · cases accepted

omit [DecidableEq Holder] in
theorem demoteUse_keeps_retentionCheck (use : Use) (address : Resource → Address)
    (heap : Heap Address Value) (captured : List Address)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : demoteUse use state = some result) :
    RequestBorrow.retentionCheck heap (roots result.next address) captured =
      RequestBorrow.retentionCheck heap (roots state address) captured := by
  rw [demoteUse_keeps_roots use address accepted]

omit [DecidableEq Holder] in
theorem forkLifetime_keeps_retentionCheck (limit : Nat) (source destination : Use)
    (address : Resource → Address) (heap : Heap Address Value) (captured : List Address)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result) :
    RequestBorrow.retentionCheck heap (roots result.next address) captured =
      RequestBorrow.retentionCheck heap (roots state address) captured :=
  RequestBorrow.retentionCheck_congr_rootAddresses heap _ _
    (forkLifetime_keeps_rootAddresses limit source destination address accepted) captured

omit [DecidableEq Holder] in
theorem detach_keeps_rootAddresses (state : State Holder Use Resource)
    (address : Resource → Address) {use : Use} (issued : use ∈ state.uses) :
    rootAddresses (roots (detach state).next address) = rootAddresses (roots state address) := by
  rw [detach_with_use state issued]
  cases retained : state.resource with
  | none => simp [roots, retained]
  | some payload =>
    rw [rootAddresses_of_use state address retained issued]
    exact rootAddresses_of_use { state with current := false, resource := some payload }
      address rfl issued

omit [DecidableEq Holder] in
theorem detach_keeps_live (state : State Holder Use Resource) (address : Resource → Address)
    (heap : Heap Address Value) {use : Use} (issued : use ∈ state.uses) (location : Address) :
    Live heap (roots (detach state).next address) location ↔
      Live heap (roots state address) location :=
  live_congr_rootAddresses heap _ _ (detach_keeps_rootAddresses state address issued) location

omit [DecidableEq Holder] in
/-- Extra roots may belong to other owners. Detachment preserves all complete
path results, including failures and repeated occurrences, while a use lives. -/
theorem detach_keeps_observations (state : State Holder Use Resource)
    (address : Resource → Address) (heap : Heap Address Value)
    (outside : Roots (Unit ⊕ Use) Address) {use : Use} (issued : use ∈ state.uses)
    (paths : List (Address × List Address))
    (live : ∀ path ∈ paths, Live heap (roots state address ∪ outside) path.1) :
    RequestBorrow.observe (collect heap (roots (detach state).next address ∪ outside)) paths =
      RequestBorrow.observe heap paths := by
  have same : rootAddresses (roots (detach state).next address ∪ outside) =
      rootAddresses (roots state address ∪ outside) := by
    simp only [rootAddresses, Finset.image_union]
    rw [show (roots (detach state).next address).image Prod.snd =
        (roots state address).image Prod.snd from detach_keeps_rootAddresses state address issued]
  unfold RequestBorrow.observe
  apply List.map_congr_left
  intro path member
  exact walk_collect heap _ ((live_congr_rootAddresses heap _ _ same path.1).mpr
    (live path member)) path.2

omit [DecidableEq Holder] in
theorem moveUse_keeps_rootAddresses (source destination : Use)
    (address : Resource → Address) {state : State Holder Use Resource}
    {result : Result Holder Use Resource} (accepted : moveUse source destination state = some result) :
    rootAddresses (roots result.next address) = rootAddresses (roots state address) := by
  unfold moveUse at accepted
  split at accepted
  · rename_i admitted
    cases Option.some.inj accepted
    cases retained : state.resource with
    | none => simp [roots, retained]
    | some payload =>
      rw [rootAddresses_of_use state address retained admitted.1]
      exact rootAddresses_of_use { state with
        uses := insert destination (state.uses.erase source)
        exclusive := if state.exclusive = some source then some destination else state.exclusive
        resource := some payload } address rfl (Finset.mem_insert_self _ _)
  · cases accepted

omit [DecidableEq Holder] in
/-- A fork creates a distinct owning edge, but adds no new reachable address.
All ordered observations of the existing graph survive, including failures. -/
theorem forkLifetime_keeps_observations (limit : Nat) (source destination : Use)
    (address : Resource → Address) (heap : Heap Address Value)
    (outside : Roots (Unit ⊕ Use) Address)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (accepted : forkLifetime limit source destination state = some result)
    (paths : List (Address × List Address))
    (live : ∀ path ∈ paths, Live heap (roots state address ∪ outside) path.1) :
    RequestBorrow.observe (collect heap (roots result.next address ∪ outside)) paths =
      RequestBorrow.observe heap paths := by
  have same : rootAddresses (roots result.next address ∪ outside) =
      rootAddresses (roots state address ∪ outside) := by
    simp only [rootAddresses, Finset.image_union]
    rw [show (roots result.next address).image Prod.snd = (roots state address).image Prod.snd
      from forkLifetime_keeps_rootAddresses limit source destination address accepted]
  unfold RequestBorrow.observe
  apply List.map_congr_left
  intro path member
  exact walk_collect heap _ ((live_congr_rootAddresses heap _ _ same path.1).mpr
    (live path member)) path.2

omit [DecidableEq Holder] in
theorem releaseUse_keeps_other_roots (use other : Use) (address : Resource → Address)
    {state : State Holder Use Resource} {result : Result Holder Use Resource}
    (different : other ≠ use) (issued : other ∈ state.uses)
    (accepted : releaseUse use state = some result) :
    other ∈ result.next.uses ∧ result.retired = none ∧
      rootAddresses (roots result.next address) = rootAddresses (roots state address) := by
  unfold releaseUse at accepted
  split at accepted
  · cases Option.some.inj accepted
    have still : other ∈ state.uses.erase use := Finset.mem_erase.mpr ⟨different, issued⟩
    have nonempty : state.uses.erase use ≠ ∅ := Finset.ne_empty_of_mem still
    simp only [extract, nonempty, and_false, if_false]
    refine ⟨still, trivial, ?_⟩
    cases retained : state.resource with
    | none => simp [roots, retained]
    | some payload =>
      rw [rootAddresses_of_use state address retained issued]
      exact rootAddresses_of_use { state with
        uses := state.uses.erase use
        exclusive := if state.exclusive = some use then none else state.exclusive
        resource := some payload } address rfl still
  · cases accepted

omit [DecidableEq Holder] in
theorem absent_roots (state : State Holder Use Resource) (address : Resource → Address)
    (absent : state.resource = none) : roots state address = ∅ := by
  simp [roots, absent]

omit [DecidableEq Holder] in
/-- After the last detached use, this owner retains no part of the graph.
Other owners are preserved by ordinary rooted collection. -/
theorem last_use_collects_only_outside (state : State Holder Use Resource) (use : Use)
    (address : Resource → Address) (heap : Heap Address Value)
    (outside : Roots (Unit ⊕ Use) Address) (valid : WellFormed state)
    (closed : state.current = false) (last : state.uses = {use})
    {result : Result Holder Use Resource} (accepted : releaseUse use state = some result)
    (location : Address) :
    (collect heap (roots result.next address ∪ outside)).lookup location =
      (collect heap outside).lookup location := by
  rw [last_use_extracts state use valid closed last] at accepted
  cases Option.some.inj accepted
  rw [absent_roots _ address rfl, Finset.empty_union]

omit [DecidableEq Holder] in
theorem last_use_reclaims (state : State Holder Use Resource) (use : Use)
    (address : Resource → Address) (heap : Heap Address Value)
    (valid : WellFormed state) (closed : state.current = false) (last : state.uses = {use})
    {result : Result Holder Use Resource} (accepted : releaseUse use state = some result)
    (location : Address) : (collect heap (roots result.next address)).lookup location = none := by
  have same := last_use_collects_only_outside state use address heap ∅ valid closed last accepted
    location
  simp only [Finset.union_empty] at same
  rw [same]
  exact lookup_collect_of_not_live heap ∅ (not_live_empty heap location)

namespace Examples

def admitted : State Nat Nat Nat := ⟨true, {0}, {7}, some 7, some 42⟩

theorem acquisition_reaches_admitted :
    acquire 2 .exclusive 0 7 (initial (Use := Nat) 0 42) = some ⟨admitted, none⟩ := by decide

theorem close_retains_admitted_and_refuses_new :
    readUse 7 (detach admitted).next = some 42 ∧
      mayMutate 7 (detach admitted).next ∧
      readHolder 0 (detach admitted).next = none ∧
      acquire 2 .exclusive 0 8 (detach admitted).next = none := by decide

theorem lifetime_is_not_exclusive_permission :
    let state : State Nat Nat Nat := ⟨true, {0}, {7}, none, some 42⟩
    readUse 7 state = some 42 ∧ ¬ mayMutate 7 state := by decide

theorem returned_lifetime_allows_next_exclusive_operation :
    let execution := run 3 admitted [.demoteUse 7, .acquire .exclusive 0 8]
    readUse 7 execution.final = some 42 ∧ ¬ mayMutate 7 execution.final ∧
      mayMutate 8 execution.final ∧ execution.accepted = 2 ∧ execution.retired = [] := by decide

theorem closed_fork_retains_memory_without_new_authority :
    let execution := run 3 admitted [.close, .forkLifetime 7 9, .demoteUse 7, .releaseUse 7]
    readUse 9 execution.final = some 42 ∧ ¬ mayMutate 9 execution.final ∧
      readHolder 0 execution.final = none ∧
      acquire 3 .exclusive 0 8 execution.final = none ∧
      execution.accepted = 4 ∧ execution.retired = [] := by decide

theorem final_fork_release_extracts_once :
    let execution := run 3 admitted
      [.close, .forkLifetime 7 9, .demoteUse 7, .releaseUse 7, .releaseUse 9]
    execution.final.resource = none ∧ execution.retired = [42] ∧
      execution.accepted = 5 ∧ execution.remaining = [] := by decide

theorem invalid_forks_and_nonexclusive_demotion_refuse :
    let lifetime : State Nat Nat Nat := ⟨false, {0}, {7}, none, some 42⟩
    forkLifetime 3 8 9 admitted = none ∧
      forkLifetime 3 7 7 admitted = none ∧
      forkLifetime 1 7 9 admitted = none ∧ demoteUse 7 lifetime = none := by decide

theorem retained_return_does_not_retry_refused_admission :
    let execution := run 3 admitted
      [.close, .forkLifetime 7 9, .demoteUse 7, .acquire .exclusive 0 8, .releaseUse 7]
    execution.accepted = 3 ∧ execution.remaining = [.acquire .exclusive 0 8, .releaseUse 7] ∧
      readUse 7 execution.final = some 42 ∧ readUse 9 execution.final = some 42 ∧
      execution.retired = [] := by decide

theorem unknown_receipt_and_wrong_holder_refuse :
    releaseUse 8 admitted = none ∧ readUse 8 admitted = none ∧
      acquire 2 .lifetime 1 8 admitted = none := by decide

theorem full_count_and_exclusive_competitor_refuse :
    acquire 1 .lifetime 0 8 admitted = none ∧
      acquire 2 .exclusive 0 8 admitted = none := by decide

theorem current_move_transfers_exclusive_permission :
    moveUse 7 8 admitted = some ⟨⟨true, {0}, {8}, some 8, some 42⟩, none⟩ ∧
      releaseUse 7 (⟨true, {0}, {8}, some 8, some 42⟩ : State Nat Nat Nat) = none := by decide

theorem closed_move_cannot_revive_currency :
    moveUse 7 8 (detach admitted).next =
      some ⟨⟨false, {0}, {8}, some 8, some 42⟩, none⟩ ∧
      acquire 2 .exclusive 0 9 (⟨false, {0}, {8}, some 8, some 42⟩ : State Nat Nat Nat) = none := by
  decide

theorem last_holder_preserves_use_until_final_release :
    let state : State Nat Nat Nat := ⟨false, ∅, {7}, some 7, some 42⟩
    releaseHolder 0 admitted = some ⟨state, none⟩ ∧
      readUse 7 state = some 42 ∧
      releaseUse 7 state = some ⟨⟨false, ∅, ∅, none, none⟩, some 42⟩ := by decide

theorem two_uses_survive_first_release_and_extract_once :
    let actions : List (Action Nat Nat) := [.acquire .exclusive 0 7, .acquire .lifetime 0 8,
      .close, .releaseUse 7, .moveUse 8 9, .releaseUse 9]
    let execution := run 2 (initial (Use := Nat) 0 42) actions
    execution.final = ⟨false, {0}, ∅, none, none⟩ ∧
      execution.retired = [42] ∧ execution.remaining = [] ∧ execution.accepted = 6 := by decide

/-- A refused close keeps itself and everything following it. -/
theorem reentrant_close_retains_complete_pending_suffix :
    let actions : List (Action Nat Nat) := [.close, .close, .acquire .lifetime 0 7]
    let execution := run 2 (initial (Use := Nat) 0 42) actions
    execution.final = ⟨false, {0}, ∅, none, none⟩ ∧ execution.retired = [42] ∧
      execution.remaining = [.close, .acquire .lifetime 0 7] ∧ execution.accepted = 1 := by decide

theorem acquisition_and_close_order_are_observably_distinct :
    let initial : State Nat Nat Nat := AcquiredUse.initial 0 42
    let first := run 2 initial [.acquire .exclusive 0 7, .close]
    let second := run 2 initial [.close, .acquire .exclusive 0 7]
    readUse 7 first.final = some 42 ∧ readUse 7 second.final = none ∧
      first.accepted = 2 ∧ second.accepted = 1 ∧
      second.remaining = [.acquire .exclusive 0 7] := by decide

end Examples

end AcquiredUse

section RelocationLifecycle

universe uDestinationValue
variable {DestinationAddress : Type} {DestinationValue : Type uDestinationValue}
variable [DecidableEq DestinationAddress]

/-- Logical owner transfer commutes with address relocation. A copied
snapshot uses its destination roots, rather than borrowing source ownership. -/
theorem Relocation.roots_transfer {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (originalOwner nextOwner : Owner) :
    copy.roots (transfer roots originalOwner nextOwner) =
      transfer (copy.roots roots) originalOwner nextOwner := by
  simp only [Relocation.roots, transfer, Finset.image_image]
  rfl

omit [DecidableEq Address] in
/-- Cancellation retains the same owner boundary after an address copy.
It cannot remove a destination root merely because its address has changed. -/
theorem Relocation.roots_cancel {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (dead : Finset Owner) :
    copy.roots (cancel roots dead) = cancel (copy.roots roots) dead := by
  ext pair
  change pair ∈ (cancel roots dead).image (fun original =>
    (original.1, copy.address original.2)) ↔ pair ∈ cancel (copy.roots roots) dead
  rw [mem_cancel]
  constructor
  · intro member
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
    have retained := (mem_cancel roots dead original).mp present
    exact ⟨Finset.mem_image.mpr ⟨original, retained.1, rfl⟩, retained.2⟩
  · rintro ⟨member, surviving⟩
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_image.mpr ⟨original,
      (mem_cancel roots dead original).mpr ⟨present, surviving⟩, rfl⟩

/-- Retiring the source owner cannot remove a copied live path from the
independently rooted destination. -/
theorem Relocation.live_after_source_retirement {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (originalOwner nextOwner : Owner) (different : nextOwner ≠ originalOwner)
    (owned : ∀ pair ∈ roots, pair.1 = originalOwner)
    (a : Address) (live : Live source roots a) :
    Live destination (release (transfer (copy.roots roots) originalOwner nextOwner)
      originalOwner) (copy.address a) := by
  rw [release_transferred_source _ originalOwner nextOwner different]
  · exact (live_transfer_iff destination (copy.roots roots) originalOwner nextOwner _).mpr
      ((copy.live_iff roots _).mpr ⟨a, live, rfl⟩)
  · intro pair member
    obtain ⟨original, present, rfl⟩ := Finset.mem_image.mp member
    exact owned original present

/-- A checked borrowed view survives collection after transferring its
existing roots and retiring the old owner. The view itself adds no roots.
All reads use the collected destination graph, including failed paths. -/
theorem RequestBorrow.transport_read_after_source_retirement
    (source : RequestBorrow.Region Owner Address Value)
    (destination : RequestBorrow.Region Owner DestinationAddress DestinationValue)
    (copy : Relocation source.heap destination.heap) (roots : Roots Owner Address)
    (different : destination.stamp.identity ≠ source.stamp.identity)
    (owned : ∀ pair ∈ roots, pair.1 = source.stamp.identity)
    (view : RequestBorrow.View Owner Address)
    (live : ∀ query ∈ view.paths, Live source.heap roots query.1) :
    (RequestBorrow.transport source destination copy view).bind
        (RequestBorrow.read { destination with
          heap := collect destination.heap
            (release (transfer (copy.roots roots) source.stamp.identity destination.stamp.identity)
              source.stamp.identity) }) =
      (RequestBorrow.read source view).map (List.map (Option.map fun pair =>
        (copy.address pair.1, pair.2.relocate copy.address copy.payload))) := by
  by_cases issued : view.stamp = source.stamp
  · simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, if_pos issued, Option.bind_some,
      RequestBorrow.read, ↓reduceIte, Option.map_some]
    congr 1
    simp only [RequestBorrow.observe, RequestBorrow.relocatePaths, List.map_map]
    apply List.map_congr_left
    intro query member
    dsimp only [Function.comp_def]
    rw [walk_collect destination.heap _ (copy.live_after_source_retirement roots
      source.stamp.identity destination.stamp.identity different owned query.1
        (live query member))]
    exact copy.walk_eq query.1 query.2
  · simp only [RequestBorrow.transport, RequestBorrow.View.transportIfCurrent, Option.bind_none, RequestBorrow.read,
      if_neg issued, Option.map_none]

end RelocationLifecycle

/-! ## Transitive memory bounds -/

def cellBytes (h : Heap Address Value) (a : Address) : Nat :=
  ((h.lookup a).map Cell.bytes).getD 0

def allocatedBytes (h : Heap Address Value) : Nat :=
  ∑ a ∈ h.allocated, cellBytes h a

noncomputable def retainedBytes (h : Heap Address Value)
    (roots : Roots Owner Address) : Nat :=
  ∑ a ∈ footprint h roots, cellBytes h a

/-- Executable byte account of the deduplicated transitive census. The chosen
cell byte profile can count live payload or retained allocation capacity; the
two profiles must be named separately by a runtime adapter. -/
def censusBytes (h : Heap Address Value) (roots : Roots Owner Address) : Nat :=
  ∑ a ∈ census h roots, cellBytes h a

omit [DecidableEq Owner] in
@[simp] theorem censusBytes_empty (heap : Heap Address Value) :
    censusBytes heap (∅ : Roots Owner Address) = 0 := by
  simp [censusBytes]

omit [DecidableEq Owner] in
theorem censusBytes_eq_retainedBytes (h : Heap Address Value)
    (roots : Roots Owner Address) (valid : ValidRoots h roots) :
    censusBytes h roots = retainedBytes h roots := by
  rw [censusBytes, census_eq_footprint h roots valid]
  rfl

omit [DecidableEq Owner] in
/-- Equal rooted address sets retain the same payload bytes. Root-table and
owner-link allocations require their own storage account. -/
theorem retainedBytes_congr_rootAddresses (h : Heap Address Value)
    (roots more : Roots Owner Address)
    (same : rootAddresses roots = rootAddresses more) :
    retainedBytes h roots = retainedBytes h more := by
  unfold retainedBytes
  rw [footprint_congr_rootAddresses h roots more same]

omit [DecidableEq Owner] in
theorem censusBytes_congr_rootAddresses (h : Heap Address Value)
    (roots more : Roots Owner Address)
    (same : rootAddresses roots = rootAddresses more) :
    censusBytes h roots = censusBytes h more := by
  unfold censusBytes
  rw [census_congr_rootAddresses h roots more same]

/-- Transfer preserves payload allocation identity and therefore payload bytes. -/
theorem retainedBytes_transfer (h : Heap Address Value) (roots : Roots Owner Address)
    (source destination : Owner) :
    retainedBytes h (transfer roots source destination) = retainedBytes h roots :=
  retainedBytes_congr_rootAddresses h _ _ (rootAddresses_transfer roots source destination)

/-- Adding a sharing owner does not duplicate the reachable payload graph. -/
theorem retainedBytes_fork (h : Heap Address Value) (roots : Roots Owner Address)
    (source destination : Owner) :
    retainedBytes h (fork roots source destination) = retainedBytes h roots :=
  retainedBytes_congr_rootAddresses h _ _ (rootAddresses_fork roots source destination)

theorem censusBytes_transfer (h : Heap Address Value) (roots : Roots Owner Address)
    (source destination : Owner) :
    censusBytes h (transfer roots source destination) = censusBytes h roots :=
  censusBytes_congr_rootAddresses h _ _ (rootAddresses_transfer roots source destination)

theorem censusBytes_fork (h : Heap Address Value) (roots : Roots Owner Address)
    (source destination : Owner) :
    censusBytes h (fork roots source destination) = censusBytes h roots :=
  censusBytes_congr_rootAddresses h _ _ (rootAddresses_fork roots source destination)

/-- Repeated retention of one immutable graph charges each reachable allocation
once. This equation does not erase the separate cost of ownership bookkeeping. -/
theorem retainedBytes_fork_list (h : Heap Address Value) (roots : Roots Owner Address)
    (source : Owner) (destinations : List Owner) :
    retainedBytes h (destinations.foldl (fun retained next => fork retained source next) roots) =
      retainedBytes h roots :=
  retainedBytes_congr_rootAddresses h _ _ (rootAddresses_fork_list roots source destinations)

theorem censusBytes_fork_list (h : Heap Address Value) (roots : Roots Owner Address)
    (source : Owner) (destinations : List Owner) :
    censusBytes h (destinations.foldl (fun retained next => fork retained source next) roots) =
      censusBytes h roots :=
  censusBytes_congr_rootAddresses h _ _ (rootAddresses_fork_list roots source destinations)

namespace PinnedReset

/-- A detached revision retains exactly the old payload allocation account.
The pin and store links have their own bookkeeping cost; neither creates a
second copy of the graph, nor makes the old revision current again. -/
theorem censusBytes_after_detach (heap : Heap Address Value)
    (old : Roots Owner Address) (store reader : Owner) (different : reader ≠ store) :
    censusBytes heap (roots old store reader) = censusBytes heap old :=
  censusBytes_congr_rootAddresses heap _ _
    (rootAddresses_release_after_fork old store reader different)

/-- Once the final reader of a detached generation releases it, that
generation contributes no retained payload bytes, including cyclic storage. -/
theorem censusBytes_after_last_reader (heap : Heap Address Value)
    (old : Roots Owner Address) (store reader : Owner)
    (owned : ∀ pair ∈ old, pair.1 = store) :
    censusBytes heap (release (roots old store reader) reader) = 0 := by
  rw [last_reader_releases old store reader owned, censusBytes_empty]

end PinnedReset

section RelocationStorage

universe uDestinationValue
variable {DestinationAddress : Type} {DestinationValue : Type uDestinationValue}
variable [DecidableEq DestinationAddress]

omit [DecidableEq Address] [DecidableEq Owner] in
theorem Relocation.cellBytes_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (a : Address) :
    cellBytes destination (copy.address a) = cellBytes source a := by
  unfold cellBytes
  rw [copy.lookup_eq]
  cases source.lookup a <;> rfl

/-- Injectivity and transported byte weights count every retained resource
once, including shared cycles. Copying work itself has a separate charge. -/
theorem Relocation.retainedBytes_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address) :
    retainedBytes destination (copy.roots roots) = retainedBytes source roots := by
  unfold retainedBytes
  rw [copy.footprint_eq, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a _
    exact copy.cellBytes_eq a
  · intro a _ b _ same
    exact copy.injective same

theorem Relocation.censusBytes_eq {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (roots : Roots Owner Address)
    (valid : ValidRoots source roots) :
    censusBytes destination (copy.roots roots) = censusBytes source roots := by
  rw [censusBytes_eq_retainedBytes _ _ (copy.valid_roots roots valid),
    censusBytes_eq_retainedBytes _ _ valid, copy.retainedBytes_eq]

end RelocationStorage

/-- Adding per-owner byte accounts overcounts exactly their shared footprint.
The combined account retains sharing rather than charging each reference. -/
theorem retainedBytes_union_overlap (h : Heap Address Value)
    (first second : Roots Owner Address) :
    retainedBytes h first + retainedBytes h second =
      retainedBytes h (first ∪ second) +
        ∑ a ∈ footprint h first ∩ footprint h second, cellBytes h a := by
  classical
  rw [retainedBytes, retainedBytes, retainedBytes, footprint_union]
  exact Finset.sum_union_inter.symm

omit [DecidableEq Owner] in
theorem retainedBytes_mono (h : Heap Address Value) {roots more : Roots Owner Address}
    (subset : roots ⊆ more) : retainedBytes h roots ≤ retainedBytes h more :=
  Finset.sum_le_sum_of_subset (footprint_mono h subset)

theorem retainedBytes_cancel_le (h : Heap Address Value) (roots : Roots Owner Address)
    (dead : Finset Owner) : retainedBytes h (cancel roots dead) ≤ retainedBytes h roots :=
  retainedBytes_mono h (cancel_subset roots dead)

omit [DecidableEq Owner] in
theorem allocatedBytes_collect (h : Heap Address Value)
    (roots : Roots Owner Address) :
    allocatedBytes (collect h roots) = retainedBytes h roots := by
  apply Finset.sum_congr rfl
  intro a member
  simp only [cellBytes,
    lookup_collect_of_live h roots ((mem_footprint h roots a).mp member)]

omit [DecidableEq Owner] in
/-- The exact live set is the union of the transitive footprint of each root. -/
theorem footprint_eq_biUnion (h : Heap Address Value) (roots : Roots Owner Address) :
    footprint h roots = roots.biUnion (fun pair => footprint h {pair}) := by
  classical
  ext a
  simp only [mem_footprint, Finset.mem_biUnion]
  exact live_iff_root h roots a

omit [DecidableEq Owner] in
/-- Root count bounds memory only together with a transitive per-root bound. -/
theorem footprint_card_le (h : Heap Address Value) (roots : Roots Owner Address)
    (perRoot : Nat)
    (bounded : ∀ pair ∈ roots, (footprint h {pair}).card ≤ perRoot) :
    (footprint h roots).card ≤ roots.card * perRoot := by
  classical
  rw [footprint_eq_biUnion]
  exact (Finset.card_biUnion_le).trans
    ((Finset.sum_le_sum bounded).trans_eq (by simp))

omit [DecidableEq Owner] in
/-- A finite footprint and a per-resource byte bound yield a byte bound. -/
theorem retainedBytes_le (h : Heap Address Value) (roots : Roots Owner Address)
    (cells bytes : Nat) (count : (footprint h roots).card ≤ cells)
    (weights : ∀ a ∈ footprint h roots, cellBytes h a ≤ bytes) :
    retainedBytes h roots ≤ cells * bytes := by
  calc
    retainedBytes h roots ≤ (footprint h roots).card * bytes := by
      exact (Finset.sum_le_sum weights).trans_eq (by simp)
    _ ≤ cells * bytes := Nat.mul_le_mul_right bytes count

omit [DecidableEq Owner] in
theorem retainedBytes_le_root_footprints (h : Heap Address Value)
    (roots : Roots Owner Address) (rootLimit perRoot bytes : Nat)
    (rootCount : roots.card ≤ rootLimit)
    (bounded : ∀ pair ∈ roots, (footprint h {pair}).card ≤ perRoot)
    (weights : ∀ a ∈ footprint h roots, cellBytes h a ≤ bytes) :
    retainedBytes h roots ≤ rootLimit * perRoot * bytes := by
  apply retainedBytes_le h roots _ bytes _ weights
  exact (footprint_card_le h roots perRoot bounded).trans
    (Nat.mul_le_mul_right perRoot rootCount)

/-! ## Shared cyclic resources and release controls -/

namespace Examples

/-- Node 0 reaches the cycle 1 -> 2 -> 1. -/
def cyclicCell (a : Fin 3) : Cell (Fin 3) Nat where
  value := a.val + 10
  references := if a = 0 then {1} else if a = 1 then {2} else {1}
  bytes := 16

def cyclicHeap : Heap (Fin 3) Nat where
  lookup a := some (cyclicCell a)
  allocated := Finset.univ
  allocated_iff a := by simp
  closed _ _ _ b _ := Finset.mem_univ b

def siblingRoots : Roots Nat (Fin 3) := {(0, 0), (1, 2)}

def cyclicUse : AcquiredUse.State Nat Nat (Fin 3) := ⟨true, {0}, {7}, some 7, some 0⟩

theorem captured_cycle_retention_check :
    RequestBorrow.retentionCheck cyclicHeap
      (AcquiredUse.roots (AcquiredUse.detach cyclicUse).next id)
      [0, 0, 1, 2] = true := by decide

theorem captured_cycle_retention_preserves_paths :
    RequestBorrow.observe (collect cyclicHeap
      (AcquiredUse.roots (AcquiredUse.detach cyclicUse).next id))
      [(0, [1, 2]), (0, [1, 2]), (0, [0])] =
      RequestBorrow.observe cyclicHeap [(0, [1, 2]), (0, [1, 2]), (0, [0])] := by
  apply RequestBorrow.retentionCheck_preserves_paths _ _ [0, 0, 1, 2]
    captured_cycle_retention_check
  intro query member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> simp

/-- Retaining a reachable tail alone cannot protect the capturing controller. -/
theorem tail_only_retention_check_refused :
    RequestBorrow.retentionCheck cyclicHeap ({(1, 2)} : Roots Nat (Fin 3)) [0] = false :=
  by decide

theorem tail_only_pin_changes_captured_observation :
    RequestBorrow.observe (collect cyclicHeap ({(1, 2)} : Roots Nat (Fin 3)))
      [(0, [1, 2])] ≠ RequestBorrow.observe cyclicHeap [(0, [1, 2])] := by
  have missing : ¬ Live cyclicHeap ({(1, 2)} : Roots Nat (Fin 3)) 0 := by
    have valid : ValidRoots cyclicHeap ({(1, 2)} : Roots Nat (Fin 3)) := by
      intro pair _
      exact Finset.mem_univ _
    have absent : (0 : Fin 3) ∉ census cyclicHeap ({(1, 2)} : Roots Nat (Fin 3)) :=
      by decide
    exact fun live => absent
      ((mem_census_iff_live cyclicHeap _ valid 0).mpr live)
  have gone := lookup_collect_of_not_live cyclicHeap _ missing
  have retired : RequestBorrow.observe
      (collect cyclicHeap ({(1, 2)} : Roots Nat (Fin 3))) [(0, [1, 2])] = [none] := by
    simp only [RequestBorrow.observe, List.map_cons, List.map_nil, walk, gone,
      Option.bind_none]
  have original : RequestBorrow.observe cyclicHeap [(0, [1, 2])] =
      [some (2, cyclicCell 2)] := by decide
  rw [retired, original]
  simp

/-- A held use protects the entire cycle, with duplicate observations and a
failed path retained in their original order. -/
theorem acquired_use_keeps_complete_cyclic_observations :
    RequestBorrow.observe (collect cyclicHeap
      (AcquiredUse.roots (AcquiredUse.detach cyclicUse).next id))
      [(0, [1, 2]), (0, [1, 2]), (0, [0])] =
      [some (2, cyclicCell 2), some (2, cyclicCell 2), none] := by
  have preserved := AcquiredUse.detach_keeps_observations cyclicUse id cyclicHeap ∅
    (use := 7) (by decide) [(0, [1, 2]), (0, [1, 2]), (0, [0])] (by
      intro path member
      have start : path.1 = 0 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> rfl
      rw [start]
      apply live_of_root cyclicHeap _ (owner := Sum.inr 7)
      · exact Finset.mem_union_left ∅ (AcquiredUse.use_rooted cyclicUse id rfl (by decide))
      · exact Finset.mem_univ 0)
  simp only [Finset.union_empty] at preserved
  rw [preserved]
  decide

theorem acquired_use_final_release_reclaims_cycle (location : Fin 3) :
    let released : AcquiredUse.Result Nat Nat (Fin 3) :=
      ⟨⟨false, {0}, ∅, none, none⟩, some 0⟩
    (collect cyclicHeap (AcquiredUse.roots released.next id)).lookup location = none := by
  apply AcquiredUse.last_use_reclaims (AcquiredUse.detach cyclicUse).next 7 id cyclicHeap
  · apply AcquiredUse.detach_wellFormed
    constructor
    · decide
    · intro use issued
      simpa only [cyclicUse, Option.some.injEq, Finset.mem_singleton] using issued.symm
  · exact AcquiredUse.detach_revokes cyclicUse
  · rfl
  · decide

/-- Two equal requested paths remain two observations after detachment. -/
theorem pinned_reset_keeps_cyclic_observations :
    RequestBorrow.observe (collect cyclicHeap
      (PinnedReset.roots ({(0, 0)} : Roots Nat (Fin 3)) 0 7))
      [(0, [1, 2]), (0, [1, 2])] =
    RequestBorrow.observe cyclicHeap [(0, [1, 2]), (0, [1, 2])] := by
  apply PinnedReset.observations_after_detach cyclicHeap _ 0 7 (by decide)
  · intro pair member
    simpa only [Finset.mem_singleton] using congrArg Prod.fst
      (Finset.mem_singleton.mp member)
  · intro path member
    have root : path.1 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at member
      exact congrArg Prod.fst member
    rw [root]
    exact live_of_root cyclicHeap ({(0, 0)} : Roots Nat (Fin 3))
      (owner := 0) (a := 0) (by simp) (Finset.mem_univ 0)

/-- Omitting the reader root makes the detached storage disappear. A surviving
space handle alone cannot keep this old observation valid. -/
theorem reset_without_pin_loses_cell :
    (collect cyclicHeap (release ({(0, 0)} : Roots Nat (Fin 3)) 0)).lookup 0 ≠
      cyclicHeap.lookup 0 := by
  have empty : release ({(0, 0)} : Roots Nat (Fin 3)) 0 = ∅ := by decide
  rw [empty, lookup_collect_of_not_live cyclicHeap ∅ (not_live_empty cyclicHeap 0)]
  simp [cyclicHeap]

/-- Cycles terminate in the existing finite closure algorithm; shared
descendants count once in the complete census. -/
theorem cyclic_census_and_bytes :
    census cyclicHeap siblingRoots = {0, 1, 2} ∧
      censusBytes cyclicHeap siblingRoots = 48 := by decide

/-- The old graph stays charged while its reader is pinned. Final release
and reset without a pin both lose that graph; neither is a zero-cost live
revision. -/
theorem pinned_reset_storage_lifecycle :
    censusBytes cyclicHeap (PinnedReset.roots ({(0, 0)} : Roots Nat (Fin 3)) 0 7) = 48 ∧
      censusBytes cyclicHeap
        (release (PinnedReset.roots ({(0, 0)} : Roots Nat (Fin 3)) 0 7) 7) = 0 ∧
      censusBytes cyclicHeap (release ({(0, 0)} : Roots Nat (Fin 3)) 0) = 0 := by
  decide

/-- Two owners of the same cycle do not create two physical copies. -/
theorem per_owner_census_overcounts_shared_cycle :
    censusBytes cyclicHeap ({(0, 1)} : Roots Nat (Fin 3)) +
      censusBytes cyclicHeap ({(1, 2)} : Roots Nat (Fin 3)) = 64 ∧
      censusBytes cyclicHeap ({(0, 1), (1, 2)} : Roots Nat (Fin 3)) = 32 := by decide

/-- The owner table grows, but the shared cyclic payload still occupies its
original three allocations. Repeated retention does not copy the payload. -/
theorem repeated_retention_shares_payload :
    (fork (fork (fork siblingRoots 0 2) 0 3) 0 2).card = 4 ∧
      siblingRoots.card = 2 ∧
      censusBytes cyclicHeap (fork (fork (fork siblingRoots 0 2) 0 3) 0 2) = 48 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [censusBytes_fork, censusBytes_fork, censusBytes_fork]
  exact cyclic_census_and_bytes.2

theorem two_paths_share_cyclic_endpoint : Aliases cyclicHeap 0 [1, 2] 2 [] := by
  refine ⟨2, ?_, ?_⟩ <;> decide

theorem failed_paths_are_not_aliases : ¬ Aliases cyclicHeap 0 [0] 2 [0] := by
  rintro ⟨endpoint, left, _⟩
  have failed : walk cyclicHeap 0 [0] = none := by decide
  simp [failed] at left

/-- A real copy shifts every address, changes the payload representation
and leaves an unrelated self-referencing destination allocation at zero. -/
def relocationAddress (a : Fin 3) : Fin 4 := ⟨a.val + 1, by omega⟩

def copiedCell (a : Fin 4) : Cell (Fin 4) Nat where
  value := a.val + 109
  references := if a = 0 then {0} else if a = 1 then {2} else if a = 2 then {3} else {2}
  bytes := 16

def copiedHeap : Heap (Fin 4) Nat where
  lookup a := some (copiedCell a)
  allocated := Finset.univ
  allocated_iff a := by simp
  closed _ _ _ b _ := Finset.mem_univ b

def shiftedCopy : Relocation cyclicHeap copiedHeap where
  address := relocationAddress
  payload n := n + 100
  injective := by
    intro a b same
    apply Fin.ext
    have values := congrArg Fin.val same
    change a.val + 1 = b.val + 1 at values
    omega
  lookup_eq := by decide +kernel

/-- The nonidentity copy retains every captured cyclic dependency; the extra
destination allocation is not needed to obtain acceptance. -/
theorem copied_retention_accepts_complete_capture :
    RequestBorrow.retentionCheck copiedHeap
      (shiftedCopy.roots (AcquiredUse.roots (AcquiredUse.detach cyclicUse).next id))
      ([0, 0, 1, 2].map relocationAddress) = true := by
  exact (shiftedCopy.retentionCheck_eq
    (AcquiredUse.roots (AcquiredUse.detach cyclicUse).next id) [0, 0, 1, 2]).trans
    captured_cycle_retention_check

/-- A larger copied heap does not turn a tail-only pin into a valid capture
of its missing controller. -/
theorem copied_retention_refuses_tail_only_pin :
    RequestBorrow.retentionCheck copiedHeap
      (shiftedCopy.roots ({(1, 2)} : Roots Nat (Fin 3)))
      ([0].map relocationAddress) = false := by
  exact (shiftedCopy.retentionCheck_eq ({(1, 2)} : Roots Nat (Fin 3)) [0]).trans
    tail_only_retention_check_refused

/-- The extra destination cell is outside the copied footprint, while
every cyclic descendant is retained and counted once. -/
theorem relocated_census_and_bytes :
    shiftedCopy.roots siblingRoots = {(0, 1), (1, 3)} ∧
      census copiedHeap (shiftedCopy.roots siblingRoots) = {1, 2, 3} ∧
      censusBytes copiedHeap (shiftedCopy.roots siblingRoots) = 48 := by decide

/-- An independently allocated copy costs storage while its source remains
retained. Relocation preserves each footprint; it does not retire the source. -/
theorem copy_with_live_source_retains_both :
    censusBytes cyclicHeap siblingRoots +
        censusBytes copiedHeap (shiftedCopy.roots siblingRoots) = 96 ∧
      censusBytes copiedHeap (shiftedCopy.roots siblingRoots) = 48 := by
  rw [cyclic_census_and_bytes.2, relocated_census_and_bytes.2.2]
  exact ⟨rfl, rfl⟩

theorem relocated_paths_keep_shared_endpoint :
    Aliases copiedHeap (relocationAddress 0) ([1, 2].map relocationAddress)
      (relocationAddress 2) (([] : List (Fin 3)).map relocationAddress) :=
  (shiftedCopy.aliases_iff 0 2 [1, 2] []).mpr two_paths_share_cyclic_endpoint

/-- Copying values and retagging roots while keeping the old references
produces a different graph, despite equal payloads at every new address. -/
def unrelocatedReferencesCell (a : Fin 4) : Cell (Fin 4) Nat :=
  { copiedCell a with references :=
    if a = 0 then {0} else if a = 1 then {1} else if a = 2 then {2} else {1} }

def unrelocatedReferencesHeap : Heap (Fin 4) Nat where
  lookup a := some (unrelocatedReferencesCell a)
  allocated := Finset.univ
  allocated_iff a := by simp
  closed _ _ _ b _ := Finset.mem_univ b

theorem copied_payloads_do_not_certify_references :
    (unrelocatedReferencesHeap.lookup 1).map Cell.value = (copiedHeap.lookup 1).map Cell.value ∧
      walk unrelocatedReferencesHeap 1 [2, 3] = none ∧
      walk copiedHeap 1 [2, 3] = some (3, copiedCell 3) := by decide

theorem copied_cycle_survives_source_retirement :
    Live copiedHeap
      (release (transfer (shiftedCopy.roots ({(0, 0)} : Roots Nat (Fin 3))) 0 7) 0)
      (relocationAddress 1) := by
  have owned : ∀ pair ∈ ({(0, 0)} : Roots Nat (Fin 3)), pair.1 = 0 := by
    intro pair member
    exact congrArg Prod.fst (Finset.mem_singleton.mp member)
  exact shiftedCopy.live_after_source_retirement ({(0, 0)} : Roots Nat (Fin 3)) 0 7
    (by decide) owned 1
    (live_step cyclicHeap ({(0, 0)} : Roots Nat (Fin 3)) (a := 0) (b := 1)
      (live_of_root cyclicHeap ({(0, 0)} : Roots Nat (Fin 3))
        (owner := 0) (a := 0) (by decide) (by decide)) rfl (by decide))

/-- Reusing the source owner identity does not authorize retiring it: the
release then removes the transferred roots too. -/
theorem retiring_same_owner_loses_copy :
    release (transfer ({(0, 1)} : Roots Nat (Fin 4)) 0 0) 0 = ∅ ∧
      ¬ Live copiedHeap (release (transfer ({(0, 1)} : Roots Nat (Fin 4)) 0 0) 0) 2 := by
  have cleared : release (transfer ({(0, 1)} : Roots Nat (Fin 4)) 0 0) 0 = ∅ := by decide
  exact ⟨cleared, cleared ▸ not_live_empty copiedHeap 2⟩

/-- The second branch protects a descendant shared with the released branch. -/
theorem shared_cycle_survives_sibling_release :
    Live cyclicHeap (release siblingRoots 0) 1 := by
  have atTwo : Live cyclicHeap (release siblingRoots 0) 2 :=
    live_of_root cyclicHeap _ (owner := 1) (by decide) (by decide)
  exact live_step cyclicHeap _ atTwo rfl (by decide)

theorem shared_lookup_survives_sibling_release :
    (collect cyclicHeap (release siblingRoots 0)).lookup 1 =
      some (cyclicCell 1) :=
  lookup_collect_of_live cyclicHeap _ shared_cycle_survives_sibling_release

/-- Both cycle nodes disappear when neither branch roots the graph. -/
theorem cycle_reclaimed_after_final_release (a : Fin 3) :
    (collect cyclicHeap (cancel siblingRoots {0, 1})).lookup a = none := by
  have cleared : cancel siblingRoots {0, 1} = ∅ := by decide
  rw [cleared, lookup_collect_none_iff]
  exact not_live_empty cyclicHeap a

/-- Omitting a still-live sibling root demonstrably destroys an observation. -/
theorem premature_release_changes_lookup :
    (collect cyclicHeap (release siblingRoots 0)).lookup 1 ≠
      (collect cyclicHeap (∅ : Roots Nat (Fin 3))).lookup 1 := by
  rw [shared_lookup_survives_sibling_release,
    lookup_collect_of_not_live cyclicHeap _ (not_live_empty cyclicHeap 1)]
  exact Option.some_ne_none _

/-- An obsolete root retained forever prevents the cycle from being reclaimed. -/
theorem discarded_root_retains_cycle :
    (collect cyclicHeap ({(0, 0)} : Roots Nat (Fin 3))).lookup 1 ≠ none ∧
    (collect cyclicHeap (∅ : Roots Nat (Fin 3))).lookup 1 = none := by
  have atZero : Live cyclicHeap ({(0, 0)} : Roots Nat (Fin 3)) 0 :=
    live_of_root cyclicHeap _ (owner := 0) (by decide) (by decide)
  have atOne : Live cyclicHeap ({(0, 0)} : Roots Nat (Fin 3)) 1 :=
    live_step cyclicHeap _ atZero rfl (by decide)
  constructor
  · rw [lookup_collect_of_live cyclicHeap _ atOne]
    exact Option.some_ne_none _
  · exact lookup_collect_of_not_live cyclicHeap _ (not_live_empty cyclicHeap 1)

/-! ## One root can protect an arbitrarily long chain -/

namespace PinnedRegion

/-- A private root points into the retained two-node external cycle. Address
three is unused until the private root moves there. -/
def cell (a : Fin 4) : Cell (Fin 4) Nat where
  value := if a = 0 then 10 else 77
  references := if a = 0 then {1} else if a = 1 then {2} else if a = 2 then {1} else ∅
  bytes := 16

def heap : Heap (Fin 4) Nat where
  lookup a := if a = 3 then none else some (cell a)
  allocated := {0, 1, 2}
  allocated_iff a := by
    by_cases vacant : a = 3
    · subst a
      simp
    · have finite : ∀ a : Fin 4, a ≠ 3 → a ∈ ({0, 1, 2} : Finset (Fin 4)) := by decide
      simp [vacant, finite a vacant]
  closed a foundCell found next reference := by
    by_cases vacant : a = 3
    · simp only [if_pos vacant] at found
      cases found
    · simp only [if_neg vacant, Option.some.injEq] at found
      subst foundCell
      have finite : ∀ root next : Fin 4, next ∈ (cell root).references →
          next ∈ ({0, 1, 2} : Finset (Fin 4)) := by decide
      exact finite a next reference

def names : Fin 4 ≃ Fin 4 := Equiv.swap 0 3
def copied : Heap (Fin 4) Nat := heap.relabel names id
def copy : Relocation heap copied := Relocation.ofEquiv heap names id
def external : Finset (Fin 4) := {1, 2}

theorem external_closed : ∀ a ∈ external, heap.dependencies a ⊆ external := by decide
theorem external_fixed : ∀ a ∈ external, copy.address a = a := by decide

/-- This is a genuine private move, with the external cells unchanged. -/
theorem private_moves_external_stays :
    copy.address 0 = 3 ∧ copied.lookup 0 = none ∧
      copied.lookup 3 = some (cell 0) ∧
      copied.lookup 1 = heap.lookup 1 ∧ copied.lookup 2 = heap.lookup 2 := by decide

/-- The moved private path still aliases a fresh external row. -/
theorem moved_cached_path_aliases_fresh_row :
    Aliases copied (copy.address 0) ([1, 2].map copy.address) 2 [] := by
  apply (copy.mixed_aliases_iff external external_closed external_fixed
    (fun _ _ _ _ => rfl) 0 2 [1, 2] [] (by decide)).mpr
  exact ⟨2, by decide, by decide⟩

/-- Keeping one root address while moving its external descendant changes the
path observation. The purported retained singleton is not reference closed. -/
theorem fixed_root_does_not_pin_descendants :
    Equiv.swap (1 : Fin 4) 3 0 = 0 ∧
      (walk (heap.relabel (Equiv.swap (1 : Fin 4) 3) id) 0 [1]) = none ∧
      (walk heap 0 [1]) = some (1, cell 1) ∧
      ¬ (∀ a ∈ ({0} : Finset (Fin 4)), heap.dependencies a ⊆ {0}) := by decide

/-- A second destination keeps the original external cycle and also allocates
a distinct copy of every source cell. Old and copied row payloads agree. -/
def duplicatedCell (a : Fin 7) : Cell (Fin 7) Nat where
  value := if a = 1 ∨ a = 5 then 11 else if a = 2 ∨ a = 6 then 12
    else if a = 4 then 10 else 0
  references := if a = 1 then {2} else if a = 2 then {1} else if a = 4 then {5}
    else if a = 5 then {6} else if a = 6 then {5} else ∅
  bytes := 16

def duplicatedHeap : Heap (Fin 7) Nat where
  lookup a := some (duplicatedCell a)
  allocated := Finset.univ
  allocated_iff a := by simp
  closed _ _ _ a _ := Finset.mem_univ a

def duplicatedAddress (a : Fin 3) : Fin 7 := ⟨a.val + 4, by omega⟩

def duplicatedCopy : Relocation cyclicHeap duplicatedHeap where
  address := duplicatedAddress
  payload := id
  injective := by
    intro a b same
    apply Fin.ext
    have equal := congrArg Fin.val same
    change a.val + 4 = b.val + 4 at equal
    omega
  lookup_eq := by decide +kernel

/-- Complete copy/copy alias preservation does not license comparison with
an original external row. Equal payloads do not repair the lost identity. -/
theorem copied_aliases_do_not_certify_fresh_identity :
    Aliases duplicatedHeap (duplicatedCopy.address 1) [] (duplicatedCopy.address 1) [] ∧
      (duplicatedHeap.lookup (duplicatedCopy.address 1)).map Cell.value =
        (duplicatedHeap.lookup 1).map Cell.value ∧
      ¬ Aliases duplicatedHeap (duplicatedCopy.address 1) [] 1 [] := by
  refine ⟨⟨5, by decide, by decide⟩, by decide, ?_⟩
  rintro ⟨endpoint, cached, fresh⟩
  have disagreement : (5 : Fin 7) ≠ 1 := by decide
  apply disagreement
  have cachedAt : (5 : Fin 7) = endpoint := by simpa [walk, duplicatedHeap,
    duplicatedCopy, duplicatedAddress] using cached
  have freshAt : (1 : Fin 7) = endpoint := by simpa [walk, duplicatedHeap] using fresh
  exact cachedAt.trans freshAt.symm

end PinnedRegion

def chainCell (last a : Nat) : Cell Nat Nat where
  value := a
  references := if a < last then {a + 1} else ∅
  bytes := 1

def chainHeap (last : Nat) : Heap Nat Nat where
  lookup a := if a ≤ last then some (chainCell last a) else none
  allocated := Finset.range (last + 1)
  allocated_iff a := by
    simp only [Finset.mem_range]
    constructor
    · intro within
      exact ⟨chainCell last a, if_pos (by omega)⟩
    · rintro ⟨c, found⟩
      split at found
      next within => omega
      next _ => cases found
  closed := by
    intro a c found b reference
    split at found
    next within =>
      cases found
      simp only [chainCell] at reference
      split at reference
      next below =>
        simp only [Finset.mem_singleton] at reference
        subst b
        exact Finset.mem_range.mpr (by omega)
      next _ => simp at reference
    next _ => cases found

def oneRoot : Roots Unit Nat := {((), 0)}

/-- Filtering an invalid root can return an empty census. Such a result
cannot satisfy the validity premise of the exact accounting theorem. -/
theorem missing_root_does_not_qualify :
    census (chainHeap 0) ({((), 7)} : Roots Unit Nat) = ∅ ∧
      ¬ ValidRoots (chainHeap 0) ({((), 7)} : Roots Unit Nat) := by
  constructor
  · decide
  · simp [ValidRoots, chainHeap]

theorem chain_reachable (last a : Nat) (within : a ≤ last) :
    Live (chainHeap last) oneRoot a := by
  induction a with
  | zero =>
      exact live_of_root _ _ (owner := ()) (by simp [oneRoot])
        (by simp [chainHeap])
  | succ a ih =>
      have previous : a ≤ last := by omega
      have found : (chainHeap last).lookup a = some (chainCell last a) := by
        simp [chainHeap, previous]
      apply live_step _ _ (ih previous) found
      simp [chainCell, show a < last by omega]

theorem chain_footprint (last : Nat) :
    footprint (chainHeap last) oneRoot = Finset.range (last + 1) := by
  ext a
  rw [mem_footprint, Finset.mem_range, Nat.lt_succ_iff]
  constructor
  · intro live
    have inside := live_allocated _ _ live
    simpa [chainHeap, Nat.lt_succ_iff] using inside
  · exact chain_reachable last a

theorem chain_retainedBytes (last : Nat) :
    retainedBytes (chainHeap last) oneRoot = last + 1 := by
  unfold retainedBytes
  rw [chain_footprint]
  calc
    ∑ a ∈ Finset.range (last + 1), cellBytes (chainHeap last) a =
        ∑ _a ∈ Finset.range (last + 1), 1 := by
      apply Finset.sum_congr rfl
      intro a member
      have within : a ≤ last := by simpa [Nat.lt_succ_iff] using member
      simp [cellBytes, chainHeap, within, chainCell]
    _ = last + 1 := by simp

/-- No proposed bound depending only on "one root" bounds retained bytes. -/
theorem one_root_unbounded (bound : Nat) :
    ∃ (h : Heap Nat Nat) (roots : Roots Unit Nat),
      roots.card = 1 ∧ bound < retainedBytes h roots := by
  refine ⟨chainHeap bound, oneRoot, ?_, ?_⟩
  · simp [oneRoot]
  · rw [chain_retainedBytes]
    omega

open RequestBorrow

noncomputable def borrowedRegion : Region Nat (Fin 4) Nat :=
  ⟨⟨7, 3⟩, collect copiedHeap ({(7, 1)} : Roots Nat (Fin 4))⟩

def grownRegion : Region Nat (Fin 4) Nat := ⟨⟨7, 3⟩, copiedHeap⟩

def duplicateBorrow : View Nat (Fin 4) := ⟨⟨7, 3⟩, [(1, [2, 3]), (1, [2, 3])]⟩

/-- Growth adds the unrelated cell zero. Both occurrences still observe the
shared descendant three; the borrowed view creates no duplicate graph. -/
theorem borrowed_growth_preserves_duplicate_descendants :
    read grownRegion duplicateBorrow =
      some [some (3, copiedCell 3), some (3, copiedCell 3)] ∧
    History borrowedRegion grownRegion := by
  constructor
  · decide
  · exact .grow (.refl borrowedRegion) copiedHeap
      (collect_extends_to_original copiedHeap ({(7, 1)} : Roots Nat (Fin 4)))

theorem borrowed_growth_agrees_with_origin :
    read grownRegion duplicateBorrow =
      some (observe borrowedRegion.heap duplicateBorrow.paths) := by
  apply read_exact borrowed_growth_preserves_duplicate_descendants.2
    duplicateBorrow rfl rfl
  intro query member
  have rootLive : Live copiedHeap ({(7, 1)} : Roots Nat (Fin 4)) 1 :=
    live_of_root _ _ (owner := 7) (by decide) (by decide)
  have rootAllocated : (1 : Fin 4) ∈ borrowedRegion.heap.allocated :=
    (mem_footprint _ _ _).mpr rootLive
  simp only [duplicateBorrow, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> exact rootAllocated

/-- Reusing the very same physical addresses for another graph changes a
descendant read. The generation check refuses that stale view. -/
theorem reset_generation_is_necessary :
    observe (chainHeap 0) [(0, [])] ≠ observe (chainHeap 1) [(0, [])] ∧
    read (reset (⟨⟨7, 0⟩, chainHeap 0⟩ : Region Nat Nat Nat) (chainHeap 1))
      (⟨⟨7, 0⟩, [(0, [])]⟩ : View Nat Nat) = none := by
  constructor
  · decide
  · exact read_reset_rejected _ _ _ rfl

/-- An equal generation in another arena is not the same lifetime. -/
theorem foreign_owner_is_rejected :
    read (⟨⟨8, 0⟩, chainHeap 1⟩ : Region Nat Nat Nat)
      (⟨⟨7, 0⟩, [(0, [])]⟩ : View Nat Nat) = none := by
  exact read_foreign_rejected _ _ (by decide)

/-! ## Checked transport of borrowed observations -/

/-- Equal logical labels are retained while the physical owners differ. -/
def copyBorrowSource : Region (Nat × Nat) (Fin 3) Nat :=
  ⟨⟨(42, 7), 3⟩, cyclicHeap⟩

def copyBorrowDestination : Region (Nat × Nat) (Fin 4) Nat :=
  ⟨⟨(42, 8), 3⟩, copiedHeap⟩

def copyBorrowView : View (Nat × Nat) (Fin 3) :=
  ⟨⟨(42, 7), 3⟩, [(0, [1, 2]), (0, [1, 2]), (0, [2])]⟩

def movedBorrowView : View (Nat × Nat) (Fin 4) :=
  ⟨⟨(42, 8), 3⟩, [(1, [2, 3]), (1, [2, 3]), (1, [3])]⟩

/-- Actual path transport preserves a repeated cyclic descendant and a
failed path, while moving both the addresses and the payload representation. -/
theorem checked_borrow_transport_observations :
    transport copyBorrowSource copyBorrowDestination shiftedCopy copyBorrowView =
        some movedBorrowView ∧
      (transport copyBorrowSource copyBorrowDestination shiftedCopy copyBorrowView).bind
        (read copyBorrowDestination) =
          some [some (3, copiedCell 3), some (3, copiedCell 3), none] := by
  exact ⟨rfl, by decide⟩

theorem checked_borrow_source_paths_live :
    ∀ query ∈ copyBorrowView.paths,
      Live cyclicHeap ({((42, 7), 0)} : Roots (Nat × Nat) (Fin 3)) query.1 := by
  intro query member
  have rootLive : Live cyclicHeap ({((42, 7), 0)} : Roots (Nat × Nat) (Fin 3)) 0 :=
    live_of_root _ _ (owner := (42, 7)) (by decide) (by decide)
  simp only [copyBorrowView, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> exact rootLive

/-- Source retirement preserves the same independently specified readout.
The already transferred root, rather than the borrow, protects the graph. -/
theorem checked_borrow_retirement_observations :
    (transport copyBorrowSource copyBorrowDestination shiftedCopy copyBorrowView).bind
      (read { copyBorrowDestination with
        heap := collect copiedHeap
          (release (transfer (shiftedCopy.roots
            ({((42, 7), 0)} : Roots (Nat × Nat) (Fin 3))) (42, 7) (42, 8)) (42, 7)) }) =
      some [some (3, copiedCell 3), some (3, copiedCell 3), none] := by
  have owned : ∀ pair ∈ ({((42, 7), 0)} : Roots (Nat × Nat) (Fin 3)),
      pair.1 = (42, 7) := by
    intro pair member
    exact congrArg Prod.fst (Finset.mem_singleton.mp member)
  calc
    _ = (read copyBorrowSource copyBorrowView).map (List.map (Option.map fun pair =>
          (shiftedCopy.address pair.1,
            pair.2.relocate shiftedCopy.address shiftedCopy.payload))) :=
      transport_read_after_source_retirement copyBorrowSource copyBorrowDestination
        shiftedCopy ({((42, 7), 0)} : Roots (Nat × Nat) (Fin 3)) (by decide) owned
        copyBorrowView checked_borrow_source_paths_live
    _ = _ := by decide

/-- Checking only the retained label would accept a foreign physical owner.
The complete source stamp refuses it despite equal labels and generations. -/
theorem checked_borrow_same_label_foreign_refused :
    copyBorrowView.stamp.identity.1 = (42, 99).1 ∧
      copyBorrowView.stamp.epoch = 3 ∧
      transport ({ copyBorrowSource with stamp := ⟨(42, 99), 3⟩ })
        copyBorrowDestination shiftedCopy copyBorrowView = none ∧
      read copyBorrowDestination movedBorrowView =
        some [some (3, copiedCell 3), some (3, copiedCell 3), none] := by decide

/-- Every old root still has a valid relocated address after this reset.
Blindly issuing the mapped view would read it; the source checker refuses. -/
theorem checked_borrow_stale_mapped_root_refused :
    transport (reset copyBorrowSource cyclicHeap) copyBorrowDestination
        shiftedCopy copyBorrowView = none ∧
      read copyBorrowDestination movedBorrowView ≠ none := by decide

/-- Even a transported view expires when its destination lifetime resets. -/
theorem checked_borrow_destination_reset_refused :
    (transport copyBorrowSource copyBorrowDestination shiftedCopy copyBorrowView).bind
      (read (reset copyBorrowDestination copiedHeap)) = none :=
  transport_destination_reset_rejected _ _ _ _ _

/-- A view never keeps an unrooted graph alive. Omitting the enclosing root
changes both successful descendant observations to failures. -/
theorem checked_borrow_missing_owner_changes_readout :
    (transport copyBorrowSource copyBorrowDestination shiftedCopy copyBorrowView).bind
      (read { copyBorrowDestination with
        heap := collect copiedHeap (∅ : Roots (Nat × Nat) (Fin 4)) }) =
      some [none, none, none] := by
  rw [checked_borrow_transport_observations.1]
  simp only [Option.bind_some, RequestBorrow.read, movedBorrowView, copyBorrowDestination,
    ↓reduceIte, observe, List.map_cons, List.map_nil, walk,
    lookup_collect_of_not_live copiedHeap _ (not_live_empty copiedHeap 1),
    Option.bind_none]

end Examples

/-! ## Stored operational and observer fields

A cell payload may be the record `StoredFields`. Its operational value and its
operational references are fields of that record. Projection is the
corresponding field projection. It is not a function from an arbitrary payload
to a replacement payload, and the two reference fields need not be disjoint.
`observeOperational` reads the stored operational field from the source heap.
-/

structure StoredFields (Address : Type) (Operational : Type) (Observer : Type) where
  operational : Operational
  observer : Option Observer
  operationalReferences : Finset Address
  observerReferences : Finset Address
  deriving DecidableEq

/-- The heap edge set is the stored reference fields, overlap included. -/
def Cell.storesFields {Operational Observer : Type}
    (cell : Cell Address (StoredFields Address Operational Observer)) : Prop :=
  cell.references =
    cell.value.operationalReferences ∪ cell.value.observerReferences

def Heap.storesFields {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) : Prop :=
  ∀ address cell, heap.lookup address = some cell → cell.storesFields

/-- Operational value, operational references and the stored byte weight. -/
def projectCell {Operational Observer : Type}
    (cell : Cell Address (StoredFields Address Operational Observer)) : Cell Address Operational where
  value := cell.value.operational
  references := cell.value.operationalReferences
  bytes := cell.bytes

omit [DecidableEq Address] in
theorem projectCell_value {Operational Observer : Type}
    (cell : Cell Address (StoredFields Address Operational Observer)) :
    (projectCell cell).value = cell.value.operational := rfl

omit [DecidableEq Address] in
theorem projectCell_references {Operational Observer : Type}
    (cell : Cell Address (StoredFields Address Operational Observer)) :
    (projectCell cell).references = cell.value.operationalReferences := rfl

omit [DecidableEq Address] in
theorem projectCell_bytes {Operational Observer : Type}
    (cell : Cell Address (StoredFields Address Operational Observer)) :
    (projectCell cell).bytes = cell.bytes := rfl

/-- Same addresses. Each stored record is replaced by its operational fields. -/
def projectHeap {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer))
    (stored : heap.storesFields) : Heap Address Operational where
  lookup address := (heap.lookup address).map projectCell
  allocated := heap.allocated
  allocated_iff address := by
    constructor
    · intro member
      obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp member
      exact ⟨projectCell cell, by simp [found]⟩
    · rintro ⟨_cell, found⟩
      obtain ⟨storedCell, looked, _⟩ := Option.map_eq_some_iff.mp found
      exact (heap.allocated_iff address).mpr ⟨storedCell, looked⟩
  closed address cell found next reference := by
    obtain ⟨storedCell, looked, same⟩ := Option.map_eq_some_iff.mp found
    apply heap.closed address storedCell looked
    rw [stored address storedCell looked]
    refine Finset.mem_union.mpr (Or.inl ?_)
    rw [← same] at reference
    simpa [projectCell] using reference

theorem projectHeap_lookup {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer))
    (stored : heap.storesFields) (address : Address) :
    (projectHeap heap stored).lookup address =
      (heap.lookup address).map projectCell := rfl

theorem projectHeap_allocated {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer))
    (stored : heap.storesFields) :
    (projectHeap heap stored).allocated = heap.allocated := rfl

theorem projectHeap_lookup_cell {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer))
    (stored : heap.storesFields) {address : Address} {cell : Cell Address Operational}
    (found : (projectHeap heap stored).lookup address = some cell) :
    ∃ storedCell, heap.lookup address = some storedCell ∧ cell = projectCell storedCell := by
  rw [projectHeap_lookup] at found
  obtain ⟨storedCell, looked, same⟩ := Option.map_eq_some_iff.mp found
  exact ⟨storedCell, looked, same.symm⟩

/-- Source readout of the stored operational field. This does not use
`projectHeap`. -/
def observeOperational {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (address : Address) :
    Option Operational :=
  (heap.lookup address).map fun cell => cell.value.operational

omit [DecidableEq Address] in
theorem observeOperational_eq_stored {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) {address : Address}
    {cell : Cell Address (StoredFields Address Operational Observer)}
    (found : heap.lookup address = some cell) :
    observeOperational heap address = some cell.value.operational := by
  simp [observeOperational, found]

theorem observeOperational_eq_projected {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (address : Address) :
    observeOperational heap address =
      ((projectHeap heap stored).lookup address).map Cell.value := by
  simp only [observeOperational, projectHeap_lookup]
  cases heap.lookup address with
  | none => rfl
  | some _ => simp [projectCell]

theorem projected_value_eq_stored_operational {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    {address : Address} {cell : Cell Address (StoredFields Address Operational Observer)}
    (found : heap.lookup address = some cell) :
    observeOperational heap address = some cell.value.operational ∧
      ((projectHeap heap stored).lookup address).map Cell.value =
        some cell.value.operational := by
  refine ⟨observeOperational_eq_stored heap found, ?_⟩
  rw [← observeOperational_eq_projected heap stored address,
    observeOperational_eq_stored heap found]

omit [DecidableEq Owner] in
/-- A target stored in both reference fields stays reachable on the projection.
The observer membership is not erased by the operational one. -/
theorem shared_operational_reference_stays {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (roots : Roots Owner Address) {holder target : Address}
    {cell : Cell Address (StoredFields Address Operational Observer)}
    (live : Live (projectHeap heap stored) roots holder)
    (found : heap.lookup holder = some cell)
    (shared : target ∈ cell.value.operationalReferences ∩ cell.value.observerReferences) :
    Live (projectHeap heap stored) roots target := by
  have looked : (projectHeap heap stored).lookup holder = some (projectCell cell) := by
    rw [projectHeap_lookup, found]
    rfl
  exact live_step (projectHeap heap stored) roots live looked (Finset.mem_inter.mp shared).1

omit [DecidableEq Owner] in
/-- An address outside the roots and outside every stored operational reference
field is not reachable on the projection. -/
theorem observer_only_not_live {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (roots : Roots Owner Address) (recording : Address)
    (notRoot : recording ∉ rootAddresses roots)
    (absent : ∀ holder cell, heap.lookup holder = some cell →
      recording ∉ cell.value.operationalReferences) :
    ¬ Live (projectHeap heap stored) roots recording := by
  intro live
  cases live with
  | root rooted => exact notRoot rooted.2
  | step _ edge =>
      obtain ⟨projected, found, reference⟩ := edge
      obtain ⟨storedCell, sourceFound, same⟩ := projectHeap_lookup_cell heap stored found
      rw [same] at reference
      exact absent _ storedCell sourceFound (by simpa [projectCell] using reference)

theorem walk_endpoint_is_stored_operational {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (path : List Address) {start endpoint : Address} {cell : Cell Address Operational}
    (success : walk (projectHeap heap stored) start path = some (endpoint, cell)) :
    observeOperational heap endpoint = some cell.value ∧
      ∃ storedCell, heap.lookup endpoint = some storedCell ∧
        cell = projectCell storedCell ∧ cell.value = storedCell.value.operational := by
  have looked := walk_success_lookup (projectHeap heap stored) path success
  obtain ⟨storedCell, sourceFound, same⟩ := projectHeap_lookup_cell heap stored looked
  refine ⟨?_, storedCell, sourceFound, same, ?_⟩
  · rw [observeOperational_eq_stored heap sourceFound, same]
    rfl
  · rw [same]
    rfl

/-- Source heap, retained outside frame, operational roots and the collected
private image. The source is not rewritten. -/
structure ProjectedFields (Operational Observer : Type) where
  source : Heap Address (StoredFields Address Operational Observer)
  outsideFrame : Roots Owner Address
  privateRoots : Roots Owner Address
  privateImage : Heap Address Operational

noncomputable def projectOptionalFields {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) :
    ProjectedFields (Address := Address) (Owner := Owner) Operational Observer where
  source := heap
  outsideFrame := outsideFrame
  privateRoots := privateRoots
  privateImage := collect (projectHeap heap stored) privateRoots

omit [DecidableEq Owner] in
theorem projectOptionalFields_spec {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) :
    let image := projectOptionalFields heap stored privateRoots outsideFrame
    image.source = heap ∧ image.outsideFrame = outsideFrame ∧
      image.privateRoots = privateRoots ∧
      image.privateImage = collect (projectHeap heap stored) privateRoots := by
  exact ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq Owner] in
theorem private_root_reads_stored_operational {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) {owner : Owner} {address : Address}
    {cell : Cell Address (StoredFields Address Operational Observer)}
    (member : (owner, address) ∈ privateRoots) (found : heap.lookup address = some cell) :
    observeOperational heap address = some cell.value.operational ∧
      (projectOptionalFields heap stored privateRoots outsideFrame).privateImage.lookup address =
        some (projectCell cell) ∧
      (projectOptionalFields heap stored privateRoots outsideFrame).source.lookup address =
        some cell := by
  have live : Live (projectHeap heap stored) privateRoots address :=
    live_of_root (projectHeap heap stored) privateRoots member
      (by rw [projectHeap_allocated]; exact (heap.allocated_iff address).mpr ⟨cell, found⟩)
  refine ⟨observeOperational_eq_stored heap found, ?_, ?_⟩
  · rw [show (projectOptionalFields heap stored privateRoots outsideFrame).privateImage =
        collect (projectHeap heap stored) privateRoots from rfl,
      lookup_collect_of_live (projectHeap heap stored) privateRoots live,
      projectHeap_lookup, found]
    rfl
  · rw [show (projectOptionalFields heap stored privateRoots outsideFrame).source = heap from rfl]
    exact found

omit [DecidableEq Owner] in
theorem walk_privateImage {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) {start : Address}
    (live : Live (projectHeap heap stored) privateRoots start) (path : List Address) :
    walk (projectOptionalFields heap stored privateRoots outsideFrame).privateImage start path =
      walk (projectHeap heap stored) start path := by
  rw [show (projectOptionalFields heap stored privateRoots outsideFrame).privateImage =
      collect (projectHeap heap stored) privateRoots from rfl]
  exact walk_collect (projectHeap heap stored) privateRoots live path

omit [DecidableEq Owner] in
theorem aliases_privateImage {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) {leftStart rightStart : Address}
    (leftLive : Live (projectHeap heap stored) privateRoots leftStart)
    (rightLive : Live (projectHeap heap stored) privateRoots rightStart)
    (left right : List Address) :
    Aliases (projectOptionalFields heap stored privateRoots outsideFrame).privateImage
        leftStart left rightStart right ↔
      Aliases (projectHeap heap stored) leftStart left rightStart right := by
  rw [show (projectOptionalFields heap stored privateRoots outsideFrame).privateImage =
      collect (projectHeap heap stored) privateRoots from rfl]
  exact aliases_collect (projectHeap heap stored) privateRoots leftLive rightLive left right

omit [DecidableEq Owner] in
theorem observer_only_reclaimed {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) (recording : Address)
    (notRoot : recording ∉ rootAddresses privateRoots)
    (absent : ∀ holder cell, heap.lookup holder = some cell →
      recording ∉ cell.value.operationalReferences) :
    (projectOptionalFields heap stored privateRoots outsideFrame).privateImage.lookup recording =
        none ∧
      (projectOptionalFields heap stored privateRoots outsideFrame).source.lookup recording =
        heap.lookup recording ∧
      observeOperational heap recording =
        ((projectOptionalFields heap stored privateRoots outsideFrame).source.lookup recording).map
          (fun cell => cell.value.operational) := by
  have dead := observer_only_not_live heap stored privateRoots recording notRoot absent
  refine ⟨?_, rfl, rfl⟩
  rw [show (projectOptionalFields heap stored privateRoots outsideFrame).privateImage =
      collect (projectHeap heap stored) privateRoots from rfl]
  exact lookup_collect_of_not_live (projectHeap heap stored) privateRoots dead

omit [DecidableEq Owner] in
/-- Reachable projected cells contain only stored operational references. -/
theorem projectHeap_omits_observer_reference {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (roots : Roots Owner Address) (recording : Address)
    (absent : ∀ holder cell, heap.lookup holder = some cell →
      recording ∉ cell.value.operationalReferences) :
    ∀ holder, Live (projectHeap heap stored) roots holder →
      ∀ cell, (projectHeap heap stored).lookup holder = some cell →
        recording ∉ cell.references := by
  intro holder _live cell found reference
  obtain ⟨storedCell, sourceFound, same⟩ := projectHeap_lookup_cell heap stored found
  rw [same] at reference
  exact absent holder storedCell sourceFound (by simpa [projectCell] using reference)

omit [DecidableEq Owner] in
theorem framed_source_keeps_stored_cell {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (privateRoots outsideFrame : Roots Owner Address) {owner : Owner} {address : Address}
    (framed : (owner, address) ∈ outsideFrame) :
    let image := projectOptionalFields heap stored privateRoots outsideFrame
    image.outsideFrame = outsideFrame ∧ (owner, address) ∈ image.outsideFrame ∧
      image.source = heap ∧ image.source.lookup address = heap.lookup address ∧
      observeOperational image.source address = observeOperational heap address := by
  exact ⟨rfl, framed, rfl, rfl, rfl⟩

/-! ### Stored seven is not an observer replacement -/

def sevenPayload (address : Fin 3) : StoredFields (Fin 3) Nat Nat :=
  if address = 0 then
    { operational := 7, observer := some 99, operationalReferences := {2},
      observerReferences := {1, 2} }
  else if address = 1 then
    { operational := 0, observer := some 99, operationalReferences := ∅,
      observerReferences := ∅ }
  else
    { operational := 7, observer := none, operationalReferences := ∅,
      observerReferences := ∅ }

def sevenCell (address : Fin 3) : Cell (Fin 3) (StoredFields (Fin 3) Nat Nat) where
  value := sevenPayload address
  references := (sevenPayload address).operationalReferences ∪
    (sevenPayload address).observerReferences
  bytes := if address = 0 then 4 else 1

def sevenHeap : Heap (Fin 3) (StoredFields (Fin 3) Nat Nat) where
  lookup address := some (sevenCell address)
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ _ _ := Finset.mem_univ _

theorem sevenHeap_stores : sevenHeap.storesFields := by
  intro address cell found
  simp only [sevenHeap, Option.some.injEq] at found
  subst found
  rfl

/-- The stored operational field is 7. The projection reads 7. Replacing that
field by the observer payload 99 is a different cell. -/
theorem stored_seven_projects_as_seven :
    observeOperational sevenHeap (0 : Fin 3) = some 7 ∧
      ((projectHeap sevenHeap sevenHeap_stores).lookup 0).map Cell.value = some 7 ∧
      ((projectHeap sevenHeap sevenHeap_stores).lookup 0).map Cell.value ≠ some 99 ∧
      (sevenHeap.lookup 0).map (fun cell => cell.value.observer) = some (some 99) ∧
      (projectHeap sevenHeap sevenHeap_stores).lookup 0 ≠
        some ({ value := 99, references := {2}, bytes := 4 } : Cell (Fin 3) Nat) := by
  have storedRead : observeOperational sevenHeap (0 : Fin 3) = some 7 := by
    simp [observeOperational, sevenHeap, sevenCell, sevenPayload]
  have projected := observeOperational_eq_projected sevenHeap sevenHeap_stores (0 : Fin 3)
  refine ⟨storedRead, ?_, ?_, ?_, ?_⟩
  · rw [← projected, storedRead]
  · rw [← projected, storedRead]
    decide
  · simp [sevenHeap, sevenCell, sevenPayload]
  · intro same
    have read := projected
    rw [storedRead] at read
    rw [same] at read
    have values : (7 : Nat) = 99 := by
      injection read
    exact absurd values (by decide)

theorem seven_operational_path :
    walk (projectHeap sevenHeap sevenHeap_stores) 0 [2] =
      some ((2 : Fin 3), projectCell (sevenCell 2)) ∧
      observeOperational sevenHeap 2 = some 7 ∧
      walk sevenHeap 0 [1] = some (1, sevenCell 1) ∧
      walk (projectHeap sevenHeap sevenHeap_stores) 0 [1] = none ∧
      Aliases (projectHeap sevenHeap sevenHeap_stores) 0 [2] 2 [] := by
  refine ⟨by decide, by decide, by decide, by decide, ⟨2, by decide, by decide⟩⟩

/-- Address 2 is in both reference fields and stays on the collected image.
Address 1 is only an observer reference and is reclaimed there. The source
cell at 0 still carries observer payload 99. -/
theorem shared_target_stays_and_observer_receipt_drops :
    (2 : Fin 3) ∈ (sevenCell 0).value.operationalReferences ∩
        (sevenCell 0).value.observerReferences ∧
      Live (projectHeap sevenHeap sevenHeap_stores) ({((), 0)} : Roots Unit (Fin 3)) 2 ∧
      observeOperational sevenHeap 2 = some 7 ∧
      ((projectOptionalFields sevenHeap sevenHeap_stores ({((), 0)} : Roots Unit (Fin 3))
        (∅ : Roots Unit (Fin 3))).privateImage.lookup 2).map Cell.value = some 7 ∧
      (projectOptionalFields sevenHeap sevenHeap_stores ({((), 0)} : Roots Unit (Fin 3))
        (∅ : Roots Unit (Fin 3))).privateImage.lookup 1 = none ∧
      (projectOptionalFields sevenHeap sevenHeap_stores ({((), 0)} : Roots Unit (Fin 3))
        (∅ : Roots Unit (Fin 3))).source.lookup 0 = sevenHeap.lookup 0 ∧
      ((projectOptionalFields sevenHeap sevenHeap_stores ({((), 0)} : Roots Unit (Fin 3))
        (∅ : Roots Unit (Fin 3))).source.lookup 0).map (fun cell => cell.value.observer) =
        some (some 99) := by
  set roots : Roots Unit (Fin 3) := {((), 0)}
  set image := projectOptionalFields sevenHeap sevenHeap_stores roots (∅ : Roots Unit (Fin 3))
  have shared : (2 : Fin 3) ∈ (sevenCell 0).value.operationalReferences ∩
      (sevenCell 0).value.observerReferences := by decide
  have found0 : sevenHeap.lookup 0 = some (sevenCell 0) := by simp [sevenHeap]
  have live0 : Live (projectHeap sevenHeap sevenHeap_stores) roots 0 :=
    live_of_root _ roots (by decide : ((), (0 : Fin 3)) ∈ roots)
      (by rw [projectHeap_allocated]; decide)
  have live2 :=
    shared_operational_reference_stays sevenHeap sevenHeap_stores roots live0 found0 shared
  have notRoot : (1 : Fin 3) ∉ rootAddresses roots := by decide
  have absent : ∀ holder cell, sevenHeap.lookup holder = some cell →
      (1 : Fin 3) ∉ cell.value.operationalReferences := by
    intro holder cell found
    simp only [sevenHeap, Option.some.injEq] at found
    subst found
    cases holder using Fin.cases with
    | zero => decide
    | succ holder =>
        cases holder using Fin.cases with
        | zero => decide
        | succ holder =>
            cases holder using Fin.cases with
            | zero => decide
            | succ holder => exact Fin.elim0 holder
  have released := observer_only_reclaimed sevenHeap sevenHeap_stores roots ∅ 1 notRoot absent
  have kept := lookup_collect_of_live (projectHeap sevenHeap sevenHeap_stores) roots live2
  have projected2 : (projectHeap sevenHeap sevenHeap_stores).lookup 2 =
      some (projectCell (sevenCell 2)) := by simp [projectHeap, sevenHeap]
  have observed2 : observeOperational sevenHeap 2 = some 7 := by
    simp [observeOperational, sevenHeap, sevenCell, sevenPayload]
  refine ⟨shared, live2, observed2, ?_, ?_, ?_, ?_⟩
  · have imageLookup : image.privateImage.lookup 2 =
        (projectHeap sevenHeap sevenHeap_stores).lookup 2 := by
      simpa [image, projectOptionalFields] using kept
    rw [imageLookup, projected2]
    simp [projectCell, sevenCell, sevenPayload]
  · simpa [image, projectOptionalFields] using released.1
  · simp [image, projectOptionalFields]
  · simp [image, projectOptionalFields, sevenHeap, sevenCell, sevenPayload]

/-! ## Framed history release

An observer notebook is one owner in a finite root set. Releasing that owner
drops its pairs. Any other owner's reachable component stays, including a
shared address and a cyclic path: reachability is the component of the
retained root, and collection preserves its cells and finite walks.

`framedHistoryRelease` splits the existing `ProjectedFields` record from the
retained observers' footprint.

* The first component is `collect` of the other observers' roots. Its
  allocation is that footprint. Retained observers read full stored cells and
  paths there, including observer payloads.
* The second component is `projectOptionalFields`. Its `privateRoots` are the
  producer and environment roots, and its `privateImage` is the operational
  projection collected at those roots. That is the forgetting computation.
  `outsideFrame` records the retained observer roots and is not part of the
  private image. `source` remains the original heap for comparison; it is not
  the retained footprint.

`projectHeap` drops every observer field, so it is not a readout for a
retained observer. These laws are a finite-heap contract for G4 physical
forgetting. Native pointer classification and erasure of a C arena stay
outside this contract.
-/

inductive HistoryRole where
  | producer
  | environment
  | observer
  deriving DecidableEq

def semanticRoots (role : Owner → HistoryRole) (roots : Roots Owner Address) :
    Roots Owner Address :=
  roots.filter fun pair =>
    role pair.1 = HistoryRole.producer ∨ role pair.1 = HistoryRole.environment

def observerRoots (role : Owner → HistoryRole) (roots : Roots Owner Address) :
    Roots Owner Address :=
  roots.filter fun pair => role pair.1 = HistoryRole.observer

omit [DecidableEq Address] [DecidableEq Owner] in
@[simp] theorem mem_semanticRoots (role : Owner → HistoryRole) (roots : Roots Owner Address)
    (pair : Owner × Address) :
    pair ∈ semanticRoots role roots ↔ pair ∈ roots ∧
      (role pair.1 = HistoryRole.producer ∨ role pair.1 = HistoryRole.environment) := by
  simp [semanticRoots]

omit [DecidableEq Address] [DecidableEq Owner] in
@[simp] theorem mem_observerRoots (role : Owner → HistoryRole) (roots : Roots Owner Address)
    (pair : Owner × Address) :
    pair ∈ observerRoots role roots ↔ pair ∈ roots ∧ role pair.1 = HistoryRole.observer := by
  simp [observerRoots]

omit [DecidableEq Address] in
/-- Removing an observer notebook does not change the producer and environment
roots. Their operational projection is independent of that observer frame. -/
theorem semanticRoots_release_observer (role : Owner → HistoryRole)
    (roots : Roots Owner Address) (notebook : Owner)
    (notebookObserver : role notebook = HistoryRole.observer) :
    semanticRoots role (release roots notebook) = semanticRoots role roots := by
  ext pair
  simp only [mem_semanticRoots, mem_release]
  constructor
  · intro kept
    exact ⟨kept.1.1, kept.2⟩
  · intro kept
    refine ⟨⟨kept.1, ?_⟩, kept.2⟩
    intro same
    rcases kept.2 with producer | environment
    · rw [same] at producer
      rw [notebookObserver] at producer
      cases producer
    · rw [same] at environment
      rw [notebookObserver] at environment
      cases environment

omit [DecidableEq Owner] in
/-- The reachable component of one root that belongs to `roots`. The root may
be shared, and the component may contain a cycle: `Live` from that pair is
any finite chain of stored references. Collection keeps every cell in the
component and every finite walk from the root. -/
theorem root_component_collected (heap : Heap Address Value) (roots : Roots Owner Address)
    {owner : Owner} {rootAddress target : Address}
    (frame : (owner, rootAddress) ∈ roots) (allocated : rootAddress ∈ heap.allocated)
    (component : Live heap {(owner, rootAddress)} target) :
    Live heap roots target ∧
      (collect heap roots).lookup target = heap.lookup target ∧
      ∀ path, walk (collect heap roots) rootAddress path = walk heap rootAddress path := by
  have targetLive :=
    live_mono heap (Finset.singleton_subset_iff.mpr frame) component
  have rootLive := live_of_root heap roots frame allocated
  refine ⟨targetLive, lookup_collect_of_live heap roots targetLive, ?_⟩
  intro path
  exact walk_collect heap roots rootLive path

/-- Releasing one owner leaves every other owner's component. The surviving
pair is proved from `release`, and the cells and walks are the component of
that retained root. -/
theorem retained_owner_component (heap : Heap Address Value) (roots : Roots Owner Address)
    (released : Owner) {owner : Owner} {rootAddress target : Address}
    (kept : owner ≠ released) (frame : (owner, rootAddress) ∈ roots)
    (allocated : rootAddress ∈ heap.allocated)
    (component : Live heap {(owner, rootAddress)} target) :
    (owner, rootAddress) ∈ release roots released ∧
      Live heap (release roots released) target ∧
      (collect heap (release roots released)).lookup target = heap.lookup target ∧
      ∀ path, walk (collect heap (release roots released)) rootAddress path =
        walk heap rootAddress path := by
  have keptFrame : (owner, rootAddress) ∈ release roots released :=
    (mem_release roots released (owner, rootAddress)).mpr ⟨frame, kept⟩
  have base := root_component_collected heap (release roots released)
    keptFrame allocated component
  exact ⟨keptFrame, base.1, base.2.1, base.2.2⟩

omit [DecidableEq Owner] in
/-- Producer and environment roots keep their operational component on the
projected heap. The component is reachability through operational references
from that root. -/
theorem semantic_owner_component {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (role : Owner → HistoryRole) (roots : Roots Owner Address) {owner : Owner}
    {rootAddress target : Address}
    (semantic : role owner = HistoryRole.producer ∨ role owner = HistoryRole.environment)
    (frame : (owner, rootAddress) ∈ roots)
    (allocated : rootAddress ∈ (projectHeap heap stored).allocated)
    (component : Live (projectHeap heap stored) {(owner, rootAddress)} target) :
    (owner, rootAddress) ∈ semanticRoots role roots ∧
      Live (projectHeap heap stored) (semanticRoots role roots) target ∧
      (collect (projectHeap heap stored) (semanticRoots role roots)).lookup target =
        (projectHeap heap stored).lookup target ∧
      ∀ path, walk (collect (projectHeap heap stored) (semanticRoots role roots))
          rootAddress path = walk (projectHeap heap stored) rootAddress path := by
  have member : (owner, rootAddress) ∈ semanticRoots role roots :=
    (mem_semanticRoots role roots (owner, rootAddress)).mpr ⟨frame, semantic⟩
  have base := root_component_collected (projectHeap heap stored) (semanticRoots role roots)
    member allocated component
  exact ⟨member, base.1, base.2.1, base.2.2⟩

/-- Other observers keep the full stored component of their roots. -/
theorem retained_observer_component (heap : Heap Address Value) (role : Owner → HistoryRole)
    (roots : Roots Owner Address) (notebook : Owner) {observer : Owner}
    {rootAddress target : Address} (observerRole : role observer = HistoryRole.observer)
    (kept : observer ≠ notebook) (frame : (observer, rootAddress) ∈ roots)
    (allocated : rootAddress ∈ heap.allocated)
    (component : Live heap {(observer, rootAddress)} target) :
    (observer, rootAddress) ∈ release (observerRoots role roots) notebook ∧
      Live heap (release (observerRoots role roots) notebook) target ∧
      (collect heap (release (observerRoots role roots) notebook)).lookup target =
        heap.lookup target ∧
      ∀ path, walk (collect heap (release (observerRoots role roots) notebook)) rootAddress path =
        walk heap rootAddress path := by
  have member : (observer, rootAddress) ∈ observerRoots role roots :=
    (mem_observerRoots role roots (observer, rootAddress)).mpr ⟨frame, observerRole⟩
  exact retained_owner_component heap (observerRoots role roots) notebook
    kept member allocated component

/-- Collected observer footprint, together with the operational projection of
the producer and environment roots. -/
noncomputable def framedHistoryRelease {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (role : Owner → HistoryRole) (roots : Roots Owner Address) (notebook : Owner) :
    Heap Address (StoredFields Address Operational Observer) ×
      ProjectedFields (Address := Address) (Owner := Owner) Operational Observer :=
  let outside := release (observerRoots role roots) notebook
  (collect heap outside,
    projectOptionalFields heap stored (semanticRoots role roots) outside)

theorem framedHistoryRelease_spec {Operational Observer : Type}
    (heap : Heap Address (StoredFields Address Operational Observer)) (stored : heap.storesFields)
    (role : Owner → HistoryRole) (roots : Roots Owner Address) (notebook : Owner)
    (notebookObserver : role notebook = HistoryRole.observer) :
    (framedHistoryRelease heap stored role roots notebook).1 =
        collect heap (release (observerRoots role roots) notebook) ∧
      (framedHistoryRelease heap stored role roots notebook).1.allocated =
        footprint heap (release (observerRoots role roots) notebook) ∧
      (∀ address, (notebook, address) ∉ release (observerRoots role roots) notebook) ∧
      semanticRoots role (release roots notebook) = semanticRoots role roots ∧
      (framedHistoryRelease heap stored role roots notebook).2.source = heap ∧
      (framedHistoryRelease heap stored role roots notebook).2.outsideFrame =
        release (observerRoots role roots) notebook ∧
      (framedHistoryRelease heap stored role roots notebook).2.privateRoots =
        semanticRoots role roots ∧
      (framedHistoryRelease heap stored role roots notebook).2.privateImage =
        collect (projectHeap heap stored) (semanticRoots role roots) := by
  refine ⟨rfl, rfl, ?_, semanticRoots_release_observer role roots notebook notebookObserver,
    rfl, rfl, rfl, rfl⟩
  intro address member
  exact ((mem_release (observerRoots role roots) notebook (notebook, address)).mp member).2 rfl

/-! ### Shared cycle, semantic edge, retained observer note -/

/-- Owners 0 and 1 both root the cyclic cell at address 1 of `cyclicHeap`. -/
def sharedCycleRoots : Roots Nat (Fin 3) := {(0, 1), (1, 1)}

/-- Owner 0 produces, owners 1 and 2 observe, and every remaining owner is an
environment. Owner 1 is the notebook released by the examples. -/
def notebookReleaseRole : Nat → HistoryRole
  | 0 => .producer
  | 1 => .observer
  | 2 => .observer
  | _ => .environment

/-- Producer 0 and environment 3 root the operational holder at address 0.
Notebook 1 and observer 2 both root the note at address 1. -/
def notebookReleaseRoots : Roots Nat (Fin 3) := {(0, 0), (1, 1), (2, 1), (3, 0)}

/-- Releasing owner 0 leaves owner 1's cyclic component, including the return
walk `1 → 2 → 1`. -/
theorem shared_owner_keeps_cyclic_cell :
    (1, (1 : Fin 3)) ∈ release sharedCycleRoots 0 ∧
      Live Examples.cyclicHeap (release sharedCycleRoots 0) 1 ∧
      Live Examples.cyclicHeap (release sharedCycleRoots 0) 2 ∧
      (collect Examples.cyclicHeap (release sharedCycleRoots 0)).lookup 1 =
        Examples.cyclicHeap.lookup 1 ∧
      (collect Examples.cyclicHeap (release sharedCycleRoots 0)).lookup 2 =
        Examples.cyclicHeap.lookup 2 ∧
      walk (collect Examples.cyclicHeap (release sharedCycleRoots 0)) 1 [2, 1] =
        some (1, Examples.cyclicCell 1) := by
  have frame : (1, (1 : Fin 3)) ∈ sharedCycleRoots := by decide
  have allocated : (1 : Fin 3) ∈ Examples.cyclicHeap.allocated := Finset.mem_univ _
  have rootLive : Live Examples.cyclicHeap ({(1, (1 : Fin 3))} : Roots Nat (Fin 3)) 1 :=
    live_of_root Examples.cyclicHeap _ (Finset.mem_singleton_self _) allocated
  have found : Examples.cyclicHeap.lookup 1 = some (Examples.cyclicCell 1) := by
    simp [Examples.cyclicHeap]
  have forward : (2 : Fin 3) ∈ (Examples.cyclicCell 1).references := by decide
  have cycleLive : Live Examples.cyclicHeap ({(1, (1 : Fin 3))} : Roots Nat (Fin 3)) 2 :=
    live_step Examples.cyclicHeap _ rootLive found forward
  have atRoot := retained_owner_component Examples.cyclicHeap sharedCycleRoots 0
    (by decide : (1 : Nat) ≠ 0) frame allocated rootLive
  have atCycle := retained_owner_component Examples.cyclicHeap sharedCycleRoots 0
    (by decide : (1 : Nat) ≠ 0) frame allocated cycleLive
  refine ⟨atRoot.1, atRoot.2.1, atCycle.2.1, atRoot.2.2.1, atCycle.2.2.1, ?_⟩
  have walkEq := atRoot.2.2.2 [2, 1]
  rw [walkEq]
  decide

/-- History address 2 has no semantic root. The producer's operational edge
keeps it in the forgetting image after the notebook root is released. The
observer-only note at address 1 is absent from that image. -/
theorem semantic_reference_keeps_history :
    (2 : Fin 3) ∉ rootAddresses (semanticRoots notebookReleaseRole notebookReleaseRoots) ∧
      semanticRoots notebookReleaseRole (release notebookReleaseRoots 1) =
        semanticRoots notebookReleaseRole notebookReleaseRoots ∧
      Live (projectHeap sevenHeap sevenHeap_stores)
        (semanticRoots notebookReleaseRole notebookReleaseRoots) 2 ∧
      (framedHistoryRelease sevenHeap sevenHeap_stores notebookReleaseRole
        notebookReleaseRoots 1).2.privateImage.lookup 2 =
        (projectHeap sevenHeap sevenHeap_stores).lookup 2 ∧
      walk (framedHistoryRelease sevenHeap sevenHeap_stores notebookReleaseRole
        notebookReleaseRoots 1).2.privateImage 0 [2] =
        some ((2 : Fin 3), projectCell (sevenCell 2)) ∧
      (framedHistoryRelease sevenHeap sevenHeap_stores notebookReleaseRole
        notebookReleaseRoots 1).2.privateImage.lookup 1 = none := by
  have notebookObserver : notebookReleaseRole 1 = HistoryRole.observer := by decide
  have frame : (0, (0 : Fin 3)) ∈ notebookReleaseRoots := by decide
  have semantic : notebookReleaseRole 0 = HistoryRole.producer ∨
      notebookReleaseRole 0 = HistoryRole.environment := by decide
  have allocated : (0 : Fin 3) ∈ (projectHeap sevenHeap sevenHeap_stores).allocated := by
    rw [projectHeap_allocated]
    exact Finset.mem_univ _
  have rootLive : Live (projectHeap sevenHeap sevenHeap_stores)
      ({(0, (0 : Fin 3))} : Roots Nat (Fin 3)) 0 :=
    live_of_root _ _ (Finset.mem_singleton_self _) allocated
  have found : sevenHeap.lookup 0 = some (sevenCell 0) := by simp [sevenHeap]
  have looked : (projectHeap sevenHeap sevenHeap_stores).lookup 0 =
      some (projectCell (sevenCell 0)) := by
    rw [projectHeap_lookup, found]
    rfl
  have edge : (2 : Fin 3) ∈ (projectCell (sevenCell 0)).references := by
    rw [projectCell_references]
    decide
  have historyLive : Live (projectHeap sevenHeap sevenHeap_stores)
      ({(0, (0 : Fin 3))} : Roots Nat (Fin 3)) 2 :=
    live_step _ _ rootLive looked edge
  have component := semantic_owner_component sevenHeap sevenHeap_stores notebookReleaseRole
    notebookReleaseRoots semantic frame allocated historyLive
  rcases framedHistoryRelease_spec sevenHeap sevenHeap_stores notebookReleaseRole
      notebookReleaseRoots 1 notebookObserver with
    ⟨_, _, _, semanticStable, _, _, _, privateImageEq⟩
  have notRoot : (2 : Fin 3) ∉
      rootAddresses (semanticRoots notebookReleaseRole notebookReleaseRoots) := by decide
  have valid : ValidRoots (projectHeap sevenHeap sevenHeap_stores)
      (semanticRoots notebookReleaseRole notebookReleaseRoots) := by
    intro _pair _member
    rw [projectHeap_allocated]
    exact Finset.mem_univ _
  have missing : (1 : Fin 3) ∉ census (projectHeap sevenHeap sevenHeap_stores)
      (semanticRoots notebookReleaseRole notebookReleaseRoots) := by decide
  have dead : ¬ Live (projectHeap sevenHeap sevenHeap_stores)
      (semanticRoots notebookReleaseRole notebookReleaseRoots) 1 :=
    fun live => missing ((mem_census_iff_live _ _ valid 1).mpr live)
  have walkEq := component.2.2.2 [2]
  refine ⟨notRoot, semanticStable, component.2.1, ?_, ?_, ?_⟩
  · rw [privateImageEq]
    exact component.2.2.1
  · rw [privateImageEq, walkEq]
    exact seven_operational_path.1
  · rw [privateImageEq]
    exact lookup_collect_of_not_live _ _ dead

/-- After notebook 1 is released, observer 2 still reads the stored note at
address 1 from the collected observer footprint, including its observer
payload. The footprint does not keep the unrelated holder at address 0.
Releasing observer 2, or reading the same root through `projectHeap`, loses
that payload. -/
theorem second_observer_reads_notebook_note :
    ((framedHistoryRelease sevenHeap sevenHeap_stores notebookReleaseRole
        notebookReleaseRoots 1).1.lookup 1).map (fun cell => cell.value.observer) =
      some (some 99) ∧
      (framedHistoryRelease sevenHeap sevenHeap_stores notebookReleaseRole
        notebookReleaseRoots 1).1.lookup 0 = none ∧
      (framedHistoryRelease sevenHeap sevenHeap_stores notebookReleaseRole
        notebookReleaseRoots 1).1.allocated =
        footprint sevenHeap (release (observerRoots notebookReleaseRole notebookReleaseRoots) 1) ∧
      (collect sevenHeap (release
        (release (observerRoots notebookReleaseRole notebookReleaseRoots) 1) 2)).lookup 1 = none ∧
      ((collect (projectHeap sevenHeap sevenHeap_stores)
        (release (observerRoots notebookReleaseRole notebookReleaseRoots) 1)).lookup 1).map
        Cell.value = some 0 := by
  have notebookObserver : notebookReleaseRole 1 = HistoryRole.observer := by decide
  have frame : (2, (1 : Fin 3)) ∈ notebookReleaseRoots := by decide
  have allocated : (1 : Fin 3) ∈ sevenHeap.allocated := Finset.mem_univ _
  have rootLive : Live sevenHeap ({(2, (1 : Fin 3))} : Roots Nat (Fin 3)) 1 :=
    live_of_root sevenHeap _ (Finset.mem_singleton_self _) allocated
  have kept := retained_observer_component sevenHeap notebookReleaseRole notebookReleaseRoots 1
    (by decide : notebookReleaseRole 2 = HistoryRole.observer)
    (by decide : (2 : Nat) ≠ 1) frame allocated rootLive
  rcases framedHistoryRelease_spec sevenHeap sevenHeap_stores notebookReleaseRole
      notebookReleaseRoots 1 notebookObserver with
    ⟨imageEq, footprintEq, _, _, _, _, _, _⟩
  have outsideEq : release (observerRoots notebookReleaseRole notebookReleaseRoots) 1 =
      ({(2, (1 : Fin 3))} : Roots Nat (Fin 3)) := by decide
  have sourceLookup : sevenHeap.lookup 1 = some (sevenCell 1) := by simp [sevenHeap]
  have note : (sevenCell 1).value.observer = some 99 := by
    simp [sevenCell, sevenPayload]
  have validOutside : ValidRoots sevenHeap ({(2, (1 : Fin 3))} : Roots Nat (Fin 3)) := by
    intro _pair _member
    exact Finset.mem_univ _
  have missingHolder : (0 : Fin 3) ∉ census sevenHeap ({(2, (1 : Fin 3))} : Roots Nat (Fin 3)) := by
    decide
  have holderDead : ¬ Live sevenHeap ({(2, (1 : Fin 3))} : Roots Nat (Fin 3)) 0 :=
    fun live => missingHolder ((mem_census_iff_live _ _ validOutside 0).mpr live)
  have dropped : release (release (observerRoots notebookReleaseRole notebookReleaseRoots) 1) 2 =
      (∅ : Roots Nat (Fin 3)) := by
    rw [outsideEq]
    decide
  have projectedAllocated : (1 : Fin 3) ∈ (projectHeap sevenHeap sevenHeap_stores).allocated := by
    rw [projectHeap_allocated]
    exact Finset.mem_univ _
  have projectedLive := live_of_root (projectHeap sevenHeap sevenHeap_stores)
    (release (observerRoots notebookReleaseRole notebookReleaseRoots) 1)
    kept.1 projectedAllocated
  have projectedLookup := lookup_collect_of_live (projectHeap sevenHeap sevenHeap_stores)
    (release (observerRoots notebookReleaseRole notebookReleaseRoots) 1) projectedLive
  have projectedCell : (projectHeap sevenHeap sevenHeap_stores).lookup 1 =
      some (projectCell (sevenCell 1)) := by
    simp [projectHeap_lookup, sevenHeap]
  refine ⟨?_, ?_, footprintEq, ?_, ?_⟩
  · rw [imageEq, kept.2.2.1, sourceLookup]
    simp [note]
  · rw [imageEq, outsideEq]
    exact lookup_collect_of_not_live sevenHeap _ holderDead
  · rw [dropped]
    exact lookup_collect_of_not_live sevenHeap _ (not_live_empty sevenHeap 1)
  · rw [projectedLookup, projectedCell]
    simp [projectCell, sevenCell, sevenPayload]

end Mettapedia.Machines.ResourceOwnership


/-!
# Admission of actual finite resource descriptors

Input rows contain observed optional headers and ordered slots. Finite checks
construct a reference-closed heap without a coherent input Heap or desired
destination as a premise. Equal repeated observations are allowed; conflicting
headers or slot orders are refused. An absent header is data, distinct from a
service which refused to provide observations.

This is a finite data admission check. Authentic capture execution, native
current-view/lifetime/Need/canonical-identity grants and validator progress or
physical prices are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.DescriptorAdmission

universe v
variable {A : Type} {V : Type v} [DecidableEq A]

abbrev Descriptor (A : Type) (V : Type v) := Option (Cell A V) × List A
abbrev Rows (A : Type) (V : Type v) := List (A × Descriptor A V)

/-- The existing association-list lookup keeps the first actual observation. -/
def lookup (rows : Rows A V) (address : A) : Option (Descriptor A V) := rows.lookup address

def header (rows : Rows A V) (address : A) : Option (Cell A V) :=
  (lookup rows address).bind Prod.fst

def slots (rows : Rows A V) (address : A) : List A :=
  ((lookup rows address).map Prod.snd).getD []

def allocated (rows : Rows A V) : Finset A :=
  (rows.map Prod.fst).toFinset.filter fun address => (header rows address).isSome = true

def consistent [DecidableEq V] (rows : Rows A V) : Bool :=
  rows.all fun row => decide (lookup rows row.1 = some row.2)

/-- Shape uses the actual ordered list; support checks every occurrence,
including repetitions. Set conversion occurs only in the reference observation. -/
def descriptorCheck (rows : Rows A V) (descriptor : Descriptor A V) : Bool :=
  match descriptor.1 with
  | none => descriptor.2.isEmpty
  | some cell => decide (descriptor.2.toFinset = cell.references) &&
      descriptor.2.all (fun child => (header rows child).isSome)

def check [DecidableEq V] (rows : Rows A V) (roots : List A) : Bool :=
  consistent rows && rows.all (fun row => descriptorCheck rows row.2) &&
    roots.all (fun address => (header rows address).isSome)

theorem lookup_mem (rows : Rows A V) (address : A) (descriptor : Descriptor A V)
    (found : lookup rows address = some descriptor) : (address, descriptor) ∈ rows := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp found
  rw [equal]
  simp

theorem header_has_row (rows : Rows A V) (address : A) (cell : Cell A V)
    (found : header rows address = some cell) :
    ∃ descriptor, lookup rows address = some descriptor ∧ descriptor.1 = some cell ∧
      (address, descriptor) ∈ rows := by
  obtain ⟨descriptor, atRow, atHeader⟩ := Option.bind_eq_some_iff.mp found
  exact ⟨descriptor, atRow, atHeader, lookup_mem rows address descriptor atRow⟩

theorem allocated_iff (rows : Rows A V) (address : A) :
    address ∈ allocated rows ↔ ∃ cell, header rows address = some cell := by
  constructor
  · intro present
    exact Option.isSome_iff_exists.mp (Finset.mem_filter.mp present).2
  · rintro ⟨cell, found⟩
    obtain ⟨descriptor, _, _, member⟩ := header_has_row rows address cell found
    apply Finset.mem_filter.mpr
    exact ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨(address, descriptor), member, rfl⟩), by simp [found]⟩

variable [DecidableEq V]

theorem check_iff (rows : Rows A V) (roots : List A) :
    check rows roots = true ↔
      (∀ row ∈ rows, lookup rows row.1 = some row.2) ∧
      (∀ row ∈ rows, descriptorCheck rows row.2 = true) ∧
      (∀ address ∈ roots, (header rows address).isSome = true) := by
  simp [check, consistent, List.all_eq_true, and_assoc]

theorem row_consistency (rows : Rows A V) (roots : List A) (passed : check rows roots = true)
    (row : A × Descriptor A V) (member : row ∈ rows) : lookup rows row.1 = some row.2 :=
  (check_iff rows roots).mp passed |>.1 row member

theorem row_shape (rows : Rows A V) (roots : List A) (passed : check rows roots = true)
    (row : A × Descriptor A V) (member : row ∈ rows) : descriptorCheck rows row.2 = true :=
  (check_iff rows roots).mp passed |>.2.1 row member

omit [DecidableEq V] in
theorem descriptor_present_fields (rows : Rows A V) (descriptor : Descriptor A V)
    (cell : Cell A V) (present : descriptor.1 = some cell)
    (checked : descriptorCheck rows descriptor = true) :
    descriptor.2.toFinset = cell.references ∧
      ∀ child ∈ descriptor.2, (header rows child).isSome = true := by
  simpa [descriptorCheck, present, List.all_eq_true] using checked

omit [DecidableEq V] in
theorem descriptor_absent_slots (rows : Rows A V) (descriptor : Descriptor A V)
    (absent : descriptor.1 = none) (checked : descriptorCheck rows descriptor = true) :
    descriptor.2 = [] := by
  simpa [descriptorCheck, absent] using checked

theorem reference_closed (rows : Rows A V) (roots : List A) (passed : check rows roots = true)
    (address : A) (cell : Cell A V) (found : header rows address = some cell)
    (child : A) (edge : child ∈ cell.references) : child ∈ allocated rows := by
  obtain ⟨descriptor, _, atHeader, member⟩ := header_has_row rows address cell found
  obtain ⟨references, supported⟩ := descriptor_present_fields rows descriptor cell atHeader
    (row_shape rows roots passed (address, descriptor) member)
  have slot : child ∈ descriptor.2 := List.mem_toFinset.mp (references.symm ▸ edge)
  exact (allocated_iff rows child).mpr (Option.isSome_iff_exists.mp (supported child slot))

/-- This actual heap is built only from finite lookup entries; closure is the
result of the executable support check rather than a caller-supplied map law. -/
def makeHeap (rows : Rows A V) (roots : List A) (passed : check rows roots = true) : Heap A V where
  lookup := header rows
  allocated := allocated rows
  allocated_iff := allocated_iff rows
  closed := reference_closed rows roots passed

theorem slots_exact (rows : Rows A V) (roots : List A) (passed : check rows roots = true)
    (address : A) :
    (slots rows address).toFinset = ((header rows address).map Cell.references).getD ∅ := by
  cases observed : lookup rows address with
  | none => simp [slots, header, observed]
  | some descriptor =>
      have member := lookup_mem rows address descriptor observed
      have checked := row_shape rows roots passed (address, descriptor) member
      cases found : descriptor.1 with
      | none =>
          have empty := descriptor_absent_slots rows descriptor found checked
          simp [slots, header, observed, found, empty]
      | some cell =>
          have fields := descriptor_present_fields rows descriptor cell found checked
          simpa [slots, header, observed, found] using fields.1

/-- Admission retains the actual input rows and ordered roots. Its only proof
field is earned by executing the finite check below, not supplied by a caller. -/
structure Checked (A : Type) (V : Type v) [DecidableEq A] [DecidableEq V] where
  rows : Rows A V
  roots : List A
  passed : check rows roots = true

def Checked.heap (checked : Checked A V) : Heap A V :=
  makeHeap checked.rows checked.roots checked.passed

def Checked.slots (checked : Checked A V) : A → List A := DescriptorAdmission.slots checked.rows

theorem Checked.slots_exact (checked : Checked A V) (address : A) :
    (checked.slots address).toFinset =
      ((checked.heap.lookup address).map Cell.references).getD ∅ :=
  DescriptorAdmission.slots_exact checked.rows checked.roots checked.passed address

theorem Checked.roots_allocated (checked : Checked A V) :
    ∀ address ∈ checked.roots, address ∈ checked.heap.allocated := by
  intro address member
  have present := (check_iff checked.rows checked.roots).mp checked.passed |>.2.2 address member
  exact (allocated_iff checked.rows address).mpr (Option.isSome_iff_exists.mp present)

/-- Every repeated row is realized, including an explicit absent observation;
no contradictory later row is silently overwritten by first-match lookup. -/
theorem Checked.realizes_row (checked : Checked A V) (address : A) (descriptor : Descriptor A V)
    (member : (address, descriptor) ∈ checked.rows) :
    checked.heap.lookup address = descriptor.1 ∧ checked.slots address = descriptor.2 := by
  have located := row_consistency checked.rows checked.roots checked.passed (address, descriptor) member
  simp [Checked.heap, makeHeap, header, Checked.slots, DescriptorAdmission.slots, located]

theorem repeated_rows_agree (rows : Rows A V) (roots : List A) (passed : check rows roots = true)
    (address : A) (first second : Descriptor A V)
    (firstMem : (address, first) ∈ rows) (secondMem : (address, second) ∈ rows) : first = second := by
  have left := row_consistency rows roots passed (address, first) firstMem
  have right := row_consistency rows roots passed (address, second) secondMem
  exact Option.some.inj (left.symm.trans right)

theorem conflicting_rows_reject (rows : Rows A V) (roots : List A) (address : A)
    (first second : Descriptor A V) (firstMem : (address, first) ∈ rows)
    (secondMem : (address, second) ∈ rows) (different : first ≠ second) : check rows roots = false := by
  apply Bool.eq_false_iff.mpr
  intro passed
  exact different (repeated_rows_agree rows roots passed address first second firstMem secondMem)

theorem missing_root_reject (rows : Rows A V) (roots : List A) (address : A)
    (required : address ∈ roots) (missing : header rows address = none) : check rows roots = false := by
  apply Bool.eq_false_iff.mpr
  intro passed
  have present := (check_iff rows roots).mp passed |>.2.2 address required
  simp [missing] at present

theorem missing_child_reject (rows : Rows A V) (roots : List A) (address child : A)
    (cell : Cell A V) (ordered : List A) (member : (address, (some cell, ordered)) ∈ rows)
    (required : child ∈ ordered) (missing : header rows child = none) : check rows roots = false := by
  apply Bool.eq_false_iff.mpr
  intro passed
  have fields := descriptor_present_fields rows (some cell, ordered) cell rfl
    (row_shape rows roots passed (address, (some cell, ordered)) member)
  have present := fields.2 child required
  simp [missing] at present

theorem mismatched_header_slots_reject (rows : Rows A V) (roots : List A) (address : A)
    (cell : Cell A V) (ordered : List A) (member : (address, (some cell, ordered)) ∈ rows)
    (different : ordered.toFinset ≠ cell.references) : check rows roots = false := by
  apply Bool.eq_false_iff.mpr
  intro passed
  exact different (descriptor_present_fields rows (some cell, ordered) cell rfl
    (row_shape rows roots passed (address, (some cell, ordered)) member)).1

theorem absent_header_with_slots_reject (rows : Rows A V) (roots : List A) (address : A)
    (ordered : List A) (member : (address, (none, ordered)) ∈ rows) (nonempty : ordered ≠ []) :
    check rows roots = false := by
  apply Bool.eq_false_iff.mpr
  intro passed
  exact nonempty (descriptor_absent_slots rows (none, ordered) rfl
    (row_shape rows roots passed (address, (none, ordered)) member))

/-- The executable admission returns the data whose heap and ordered-slot
realization were derived above. Failed checks return no substitute heap. -/
def admitRows (rows : Rows A V) (roots : List A) : Option (Checked A V) :=
  if passed : check rows roots = true then some ⟨rows, roots, passed⟩ else none

theorem admit_isSome (rows : Rows A V) (roots : List A) :
    (admitRows rows roots).isSome = check rows roots := by
  cases passed : check rows roots <;> simp [admitRows, passed]

theorem admit_of_passed (rows : Rows A V) (roots : List A) (passed : check rows roots = true) :
    admitRows rows roots = some ⟨rows, roots, passed⟩ := by simp [admitRows, passed]

theorem admit_of_rejected (rows : Rows A V) (roots : List A) (rejected : check rows roots = false) :
    admitRows rows roots = none := by simp [admitRows, rejected]

theorem admit_admitted (rows : Rows A V) (roots : List A) (checked : Checked A V)
    (issued : admitRows rows roots = some checked) :
    checked.rows = rows ∧ checked.roots = roots ∧ check rows roots = true := by
  unfold admitRows at issued
  split at issued
  · rename_i passed
    cases issued
    exact ⟨rfl, rfl, passed⟩
  · cases issued

theorem admitted_heap_is_actual_rows (rows : Rows A V) (roots : List A) (checked : Checked A V)
    (issued : admitRows rows roots = some checked) (address : A) :
    checked.heap.lookup address = header rows address ∧
      checked.heap.allocated = allocated rows ∧ checked.slots address = slots rows address ∧
      checked.roots = roots := by
  obtain ⟨sameRows, sameRoots, _⟩ := admit_admitted rows roots checked issued
  exact ⟨congrArg (fun data => header data address) sameRows,
    congrArg allocated sameRows, congrArg (fun data => slots data address) sameRows, sameRoots⟩

theorem Checked.no_unrecorded_cells (checked : Checked A V) (address : A) (cell : Cell A V)
    (found : checked.heap.lookup address = some cell) :
    ∃ descriptor, (address, descriptor) ∈ checked.rows ∧ descriptor.1 = some cell := by
  obtain ⟨descriptor, _, atHeader, member⟩ := header_has_row checked.rows address cell found
  exact ⟨descriptor, member, atHeader⟩

theorem Checked.recorded_slot (checked : Checked A V) (address : A) (cell : Cell A V)
    (ordered : List A) (member : (address, (some cell, ordered)) ∈ checked.rows)
    (index : Nat) (child : A) (atSlot : ordered[index]? = some child) :
    (checked.slots address)[index]? = some child ∧ child ∈ checked.heap.allocated := by
  have actual := checked.realizes_row address (some cell, ordered) member
  have inSlots : child ∈ ordered := by
    obtain ⟨bound, equal⟩ := List.getElem?_eq_some_iff.mp atSlot
    exact equal ▸ List.getElem_mem bound
  have supported := descriptor_present_fields checked.rows (some cell, ordered) cell rfl
    (row_shape checked.rows checked.roots checked.passed (address, (some cell, ordered)) member)
  exact ⟨actual.2 ▸ atSlot,
    (allocated_iff checked.rows child).mpr (Option.isSome_iff_exists.mp (supported.2 child inSlots))⟩

universe w
inductive Error (Refusal : Type w) where
  | serviceRefused (cause : Refusal)
  | invalidRows
  deriving DecidableEq

/-- A service refusal is outside the descriptor's optional header. It cannot
be reinterpreted as an ordinary absent resource or an empty successful capture. -/
def admitService {Refusal : Type w} (input : Except Refusal (Rows A V)) (roots : List A) :
    Except (Error Refusal) (Checked A V) :=
  match input with
  | .error cause => .error (.serviceRefused cause)
  | .ok rows => match admitRows rows roots with
    | none => .error .invalidRows
    | some checked => .ok checked

theorem service_refusal {Refusal : Type w} (cause : Refusal) (roots : List A) :
    admitService (V := V) (.error cause) roots = .error (.serviceRefused cause) := rfl

theorem service_refusal_is_not_success {Refusal : Type w} (cause : Refusal) (roots : List A) (checked : Checked A V) :
    admitService (.error cause) roots ≠ .ok checked := by
  intro impossible
  cases impossible

theorem service_accepted {Refusal : Type w} (rows : Rows A V) (roots : List A)
    (passed : check rows roots = true) :
    admitService (Refusal := Refusal) (.ok rows) roots = .ok ⟨rows, roots, passed⟩ := by
  simp [admitService, admit_of_passed rows roots passed]

theorem service_invalid_rows {Refusal : Type w} (rows : Rows A V) (roots : List A)
    (rejected : check rows roots = false) :
    admitService (Refusal := Refusal) (.ok rows) roots = .error .invalidRows := by
  simp [admitService, admit_of_rejected rows roots rejected]

namespace Controls

private def cell (value : Nat) (ordered : List Nat) : Cell Nat Nat := ⟨value, ordered.toFinset, 8⟩
private def row (address value : Nat) (ordered : List Nat) : Nat × Descriptor Nat Nat :=
  (address, (some (cell value ordered), ordered))
private def selfRows := [row 0 7 [0]]
private def mutualRows := [row 0 7 [1], row 1 9 [0]]
private def sharedRows := [row 0 7 [1, 1], row 1 9 []]

theorem empty_capture_admits_empty_heap :
    (admitRows ([] : Rows Nat Nat) []).isSome = true ∧
      (admitRows ([] : Rows Nat Nat) []).map (fun checked => checked.heap.allocated.card) = some 0 := by decide

theorem root_presence_alone_does_not_admit_missing_child :
    ([0] : List Nat).all (fun address => (header [row 0 7 [1]] address).isSome) = true ∧
      check [row 0 7 [1]] [0] = false := by decide

theorem transitive_missing_descendant_is_rejected :
    check [row 0 7 [1], row 1 9 [2]] [0] = false := by decide

theorem explicit_absent_child_is_not_complete_support :
    lookup [row 0 7 [1], (1, (none, []))] 1 = some (none, []) ∧
      check [row 0 7 [1], (1, (none, []))] [0] = false := by decide

theorem missing_root_is_rejected : check ([] : Rows Nat Nat) [0] = false := by decide

theorem explicitly_absent_root_is_rejected :
    check ([(0, (none, []))] : Rows Nat Nat) [0] = false := by decide

theorem self_cycle_admits_with_actual_backedge :
    (admitRows selfRows [0]).isSome = true ∧
      (admitRows selfRows [0]).map (fun checked => checked.slots 0) = some [0] ∧
      (admitRows selfRows [0]).map (fun checked => checked.heap.allocated.card) = some 1 := by decide

theorem mutual_cycle_admits_both_directions :
    (admitRows mutualRows [0]).isSome = true ∧
      (admitRows mutualRows [0]).map (fun checked => (checked.slots 0, checked.slots 1)) = some ([1], [0]) ∧
      (admitRows mutualRows [0]).map (fun checked => checked.heap.allocated.card) = some 2 := by decide

theorem mutual_cycle_with_absent_peer_is_rejected :
    check [row 0 7 [1], (1, (none, []))] [0] = false := by decide

theorem equal_repeated_observations_are_accepted :
    (admitRows [row 0 7 [0], row 0 7 [0]] [0, 0]).isSome = true ∧
      (admitRows [row 0 7 [0], row 0 7 [0]] [0, 0]).map
        (fun checked => (checked.rows.length, checked.heap.allocated.card, checked.roots)) = some (2, 1, [0, 0]) := by decide

theorem arbitrary_equal_repeats_are_accepted (count : Nat) :
    check (List.replicate (count + 1) (row 0 7 [0])) [0, 0] = true := by
  simp [check, consistent, descriptorCheck, header, lookup, row, cell,
    List.replicate_succ, List.lookup_cons]

theorem conflicting_header_payload_is_rejected :
    check [row 0 7 [0], row 0 8 [0]] [0] = false := by decide

theorem conflicting_header_bytes_are_rejected :
    check [(0, (some (cell 7 []), [])),
      (0, (some {cell 7 [] with bytes := 9}, []))] ([] : List Nat) = false := by decide

private def reorderedRows : Rows Nat Nat :=
  [(0, (some (cell 7 [1, 2]), [1, 2])), (0, (some (cell 7 [1, 2]), [2, 1])),
    row 1 9 [], row 2 9 []]

theorem header_equal_reordered_slots_are_conflicting :
    (reorderedRows[0]?).map (fun r => r.2.1) = (reorderedRows[1]?).map (fun r => r.2.1) ∧
      consistent reorderedRows = false ∧ check reorderedRows [0] = false := by
  exact ⟨rfl, by decide, by decide⟩

theorem absent_then_present_observation_is_conflicting :
    check [(0, (none, [])), row 0 7 []] ([] : List Nat) = false := by decide

theorem present_then_absent_observation_is_conflicting :
    check [row 0 7 [], (0, (none, []))] ([] : List Nat) = false := by decide

theorem header_slot_disagreement_is_rejected :
    check [(0, (some (cell 7 [1]), [])), row 1 9 []] [0] = false := by decide

theorem absent_header_cannot_declare_children :
    check ([(0, (none, [0]))] : Rows Nat Nat) [] = false := by decide

theorem duplicate_slots_keep_order_and_multiplicity :
    (admitRows sharedRows [0]).isSome = true ∧
      (admitRows sharedRows [0]).map (fun checked => checked.slots 0) = some [1, 1] ∧
      (admitRows sharedRows [0]).map (fun checked => checked.heap.allocated.card) = some 2 := by decide

theorem equal_values_do_not_collapse_distinct_resource_identities :
    (admitRows [row 0 7 [], row 1 7 []] [1, 0, 1]).map
      (fun checked => (checked.heap.allocated.card, checked.roots)) = some (2, [1, 0, 1]) := by decide

theorem ordinary_absence_is_retained_without_allocation :
    (admitRows ([(4, (none, []))] : Rows Nat Nat) []).isSome = true ∧
      (admitRows ([(4, (none, []))] : Rows Nat Nat) []).map
        (fun checked => (lookup checked.rows 4, checked.heap.lookup 4, checked.heap.allocated.card)) =
          some (some (none, []), none, 0) := by decide

theorem service_refusal_is_not_ordinary_absence :
    (admitRows ([(4, (none, []))] : Rows Nat Nat) []).isSome = true ∧
      admitService (A := Nat) (V := Nat) (.error ()) [] = .error (.serviceRefused ()) := by
  exact ⟨by decide, rfl⟩

theorem invalid_observations_are_not_an_empty_success :
    admitService (Refusal := Unit) (.ok [row 0 7 [1]]) [0] = .error .invalidRows :=
  service_invalid_rows [row 0 7 [1]] [0] (by decide)

end Controls

end Mettapedia.Machines.ResourceOwnership.DescriptorAdmission

/-!
## Conditional identity separation and scalar comparison policies

The following observations read the abstract `Cell.value`, not a recursive
State graph. A payload write preserves the stored outgoing references, byte
weight and allocation. Read and mutation admission are separate finite sets;
neither payload equality nor allocation supplies either permission.

Write-hole/read-anchor probes use those actual heap operations. Their identity
separation theorem requires two distinguishable values, live resources, both
write grants and a read grant for a discriminating alias. It does not apply to
all restricted or frozen observers. No global language equality or conversion
rule is chosen here.

Identity comparison, explicitly world-indexed scalar comparison, and a pure
comparison captured from an immutable heap coexist below. A fixed comparator
cannot also promise to track independently mutable current payloads. This
does not require every legitimate comparison policy to license substitution
through writes. Constraint/unification policies, linear or persistent State
designs, recursive graph equality and bisimulation need separate constructions.
-/

namespace Mettapedia.Machines.ResourceOwnership

open Mettapedia.GSLT.Dynamics.StoreReachability (Reach)

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} [DecidableEq Address]

/-- One scalar observation in the explicitly selected heap. -/
def Heap.readPayload (heap : Heap Address Value) (address : Address) : Option Value :=
  (heap.lookup address).map Cell.value

/-- Update the payload of an existing cell. Missing addresses remain missing;
allocation and all outgoing references and byte weights stay unchanged. -/
def Heap.writePayload (heap : Heap Address Value) (address : Address) (value : Value) :
    Heap Address Value where
  lookup query := if query = address then
    (heap.lookup query).map (fun cell => { cell with value := value }) else heap.lookup query
  allocated := heap.allocated
  allocated_iff query := by
    by_cases same : query = address
    · simp only [same, if_true]
      constructor
      · intro live
        obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp live
        exact ⟨{ cell with value := value }, by rw [found, Option.map_some]⟩
      · rintro ⟨cell, found⟩
        obtain ⟨original, present, _⟩ := Option.map_eq_some_iff.mp found
        exact (heap.allocated_iff address).mpr ⟨original, present⟩
    · simpa only [same, if_false] using heap.allocated_iff query
  closed query cell found next reference := by
    by_cases same : query = address
    · simp only [same, if_true] at found
      obtain ⟨original, present, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      exact heap.closed address original present next reference
    · simp only [same, if_false] at found
      exact heap.closed query cell found next reference

@[simp] theorem Heap.writePayload_lookup_same (heap : Heap Address Value)
    (address : Address) (value : Value) :
    (heap.writePayload address value).lookup address =
      (heap.lookup address).map (fun cell => { cell with value := value }) := by
  simp [Heap.writePayload]

theorem Heap.writePayload_lookup_other (heap : Heap Address Value)
    (address query : Address) (value : Value) (different : query ≠ address) :
    (heap.writePayload address value).lookup query = heap.lookup query := by
  simp [Heap.writePayload, different]

@[simp] theorem Heap.writePayload_allocated (heap : Heap Address Value)
    (address : Address) (value : Value) :
    (heap.writePayload address value).allocated = heap.allocated := rfl

theorem Heap.writePayload_dependencies (heap : Heap Address Value)
    (address query : Address) (value : Value) :
    (heap.writePayload address value).dependencies query = heap.dependencies query := by
  by_cases same : query = address
  · subst query
    cases found : heap.lookup address <;> simp [Heap.dependencies, found]
  · rw [Heap.dependencies, Heap.writePayload_lookup_other heap address query value same]
    rfl

theorem Heap.writePayload_bytes (heap : Heap Address Value)
    (address query : Address) (value : Value) :
    ((heap.writePayload address value).lookup query).map Cell.bytes =
      (heap.lookup query).map Cell.bytes := by
  by_cases same : query = address
  · subst query
    cases found : heap.lookup address <;> simp [found]
  · rw [Heap.writePayload_lookup_other heap address query value same]

/-- Scalar writes retain the existing reachability graph and owner roots.
Allocation is unchanged and every actual edge keeps its stored target. -/
theorem Heap.writePayload_live_iff {Owner : Type uOwner} (heap : Heap Address Value)
    (roots : Roots Owner Address) (address : Address) (value : Value) (query : Address) :
    Live (heap.writePayload address value) roots query ↔ Live heap roots query := by
  have edges : ∀ start next,
      ((heap.writePayload address value).toStore roots).pointsTo start next ↔
        (heap.toStore roots).pointsTo start next := by
    intro start next
    by_cases same : start = address
    · subst start
      cases found : heap.lookup address <;> simp [Heap.toStore, found]
    · simp only [Heap.toStore, Heap.writePayload_lookup_other heap address start value same]
  constructor
  · intro live
    exact Reach.map (source := (heap.writePayload address value).toStore roots)
      (target := heap.toStore roots) id (fun _ rooted => rooted)
      (fun start next edge => (edges start next).mp edge) live
  · intro live
    exact Reach.map (source := heap.toStore roots)
      (target := (heap.writePayload address value).toStore roots) id (fun _ rooted => rooted)
      (fun start next edge => (edges start next).mpr edge) live

/-- The exact existing ordered slot function remains a realization of the
stored references after a scalar write. No slot is rebuilt or reordered. -/
theorem DescriptorAdmission.Checked.slots_writePayload [DecidableEq Value]
    (checked : DescriptorAdmission.Checked Address Value) (address query : Address) (value : Value) :
    (checked.slots query).toFinset =
      (checked.heap.writePayload address value).dependencies query := by
  rw [Heap.writePayload_dependencies]
  exact checked.slots_exact query

theorem Heap.readPayload_write_same (heap : Heap Address Value)
    (address : Address) (value : Value) (live : address ∈ heap.allocated) :
    (heap.writePayload address value).readPayload address = some value := by
  obtain ⟨cell, found⟩ := (heap.allocated_iff address).mp live
  simp [Heap.readPayload, found]

theorem Heap.readPayload_write_other (heap : Heap Address Value)
    (address query : Address) (value : Value) (different : query ≠ address) :
    (heap.writePayload address value).readPayload query = heap.readPayload query := by
  rw [Heap.readPayload, Heap.writePayload_lookup_other heap address query value different]
  rfl

/-- An actual scalar write outside an observed support preserves every ordered
read occurrence. Cached observations do not all become invalid after a write. -/
theorem Heap.readPayload_list_write_outside (heap : Heap Address Value)
    (address : Address) (value : Value) (queries : List Address)
    (outside : address ∉ queries) :
    queries.map (heap.writePayload address value).readPayload = queries.map heap.readPayload := by
  apply List.map_congr_left
  intro query member
  apply Heap.readPayload_write_other
  intro same
  exact outside (same ▸ member)

theorem walk_addresses_writePayload (heap : Heap Address Value)
    (address : Address) (value : Value) (start : Address) (path : List Address) :
    (walk (heap.writePayload address value) start path).map Prod.fst =
      (walk heap start path).map Prod.fst := by
  induction path generalizing start with
  | nil =>
      by_cases same : start = address
      · subst start
        cases found : heap.lookup address <;> simp [walk, found]
      · simp only [walk, Heap.writePayload_lookup_other heap address start value same]
  | cons next rest ih =>
      by_cases same : start = address
      · subst start
        cases found : heap.lookup address with
        | none => simp [walk, found]
        | some cell =>
            simp only [walk, Heap.writePayload_lookup_same, found, Option.map_some,
              Option.bind_some]
            split
            next _ => exact ih next
            next _ => rfl
      · cases found : heap.lookup start with
        | none => simp [walk, Heap.writePayload_lookup_other heap address start value same, found]
        | some cell =>
            simp only [walk, Heap.writePayload_lookup_other heap address start value same,
              found, Option.bind_some]
            split
            next _ => exact ih next
            next _ => rfl

/-- Scalar mutation changes contents, while successful path alias identity is
preserved and reflected, including cycles and repeated path occurrences. -/
theorem aliases_writePayload (heap : Heap Address Value) (address : Address) (value : Value)
    (leftStart rightStart : Address) (left right : List Address) :
    Aliases (heap.writePayload address value) leftStart left rightStart right ↔
      Aliases heap leftStart left rightStart right := by
  unfold Aliases
  rw [walk_addresses_writePayload, walk_addresses_writePayload]

namespace MutableObservation

/-- Fixed-heap scalar observations, including observable absence. This is not
resource identity, authority or recursive graph equality. -/
def PayloadEq (heap : Heap Address Value) (left right : Address) : Prop :=
  heap.readPayload left = heap.readPayload right

instance instDecidablePayloadEq [DecidableEq Value] (heap : Heap Address Value)
    (left right : Address) : Decidable (PayloadEq heap left right) :=
  inferInstanceAs (Decidable (heap.readPayload left = heap.readPayload right))

omit [DecidableEq Address] in
theorem payloadEq_equivalence (heap : Heap Address Value) : Equivalence (PayloadEq heap) := by
  exact ⟨fun _ => rfl, fun equal => equal.symm, fun first second => first.trans second⟩

omit [DecidableEq Address] in
theorem payloadEq_readout {Result : Type} (heap : Heap Address Value)
    (observe : Option Value → Result) {left right : Address} (same : PayloadEq heap left right) :
    observe (heap.readPayload left) = observe (heap.readPayload right) :=
  congrArg observe same

/-- A fixed observer remains valid when the actual mutation misses both of its
resource dependencies. The heap index is explicit in both sides of the law. -/
theorem payloadEq_write_outside (heap : Heap Address Value) (address : Address) (value : Value)
    (left right : Address) (leftOther : left ≠ address) (rightOther : right ≠ address) :
    PayloadEq (heap.writePayload address value) left right ↔ PayloadEq heap left right := by
  unfold PayloadEq
  rw [Heap.readPayload_write_other heap address left value leftOther,
    Heap.readPayload_write_other heap address right value rightOther]

/-- Compose an admitted write at the hole with an admitted scalar read at the
fixed anchor. Inadmitted contexts return `none`; a fully admitted live context
always returns a value. The permission sets are supplied independently. -/
def writeRead (heap : Heap Address Value) (writes reads : Finset Address)
    (hole anchor : Address) (value : Value) : Option Value :=
  if hole ∈ writes ∧ anchor ∈ reads ∧ hole ∈ heap.allocated ∧ anchor ∈ heap.allocated then
    (heap.writePayload hole value).readPayload anchor else none

theorem writeRead_same (heap : Heap Address Value) (writes reads : Finset Address)
    (address : Address) (value : Value) (writable : address ∈ writes) (readable : address ∈ reads)
    (live : address ∈ heap.allocated) :
    writeRead heap writes reads address address value = some value := by
  simp only [writeRead, writable, readable, live, and_self, if_true]
  exact Heap.readPayload_write_same heap address value live

theorem writeRead_other (heap : Heap Address Value) (writes reads : Finset Address)
    (hole anchor : Address) (value : Value) (writable : hole ∈ writes) (readable : anchor ∈ reads)
    (holeLive : hole ∈ heap.allocated) (anchorLive : anchor ∈ heap.allocated)
    (different : anchor ≠ hole) :
    writeRead heap writes reads hole anchor value = heap.readPayload anchor := by
  simp only [writeRead, writable, readable, holeLive, anchorLive, and_self, if_true]
  exact Heap.readPayload_write_other heap hole anchor value different

theorem writeRead_admitted_isSome (heap : Heap Address Value) (writes reads : Finset Address)
    (hole anchor : Address) (value : Value) (writable : hole ∈ writes) (readable : anchor ∈ reads)
    (holeLive : hole ∈ heap.allocated) (anchorLive : anchor ∈ heap.allocated) :
    (writeRead heap writes reads hole anchor value).isSome = true := by
  by_cases same : anchor = hole
  · subst anchor
    rw [writeRead_same heap writes reads hole value writable readable holeLive]
    rfl
  · rw [writeRead_other heap writes reads hole anchor value writable readable holeLive
      anchorLive same]
    obtain ⟨cell, found⟩ := (heap.allocated_iff anchor).mp anchorLive
    simp [Heap.readPayload, found]

/-- Agreement in the concrete write-hole/read-anchor probes. The observer's
admitted mutation and read sets stay fixed when the hole is replaced. -/
def WriteReadEq (heap : Heap Address Value) (writes reads : Finset Address)
    (left right : Address) : Prop :=
  ∀ (value : Value) (anchor : Address),
    writeRead heap writes reads left anchor value = writeRead heap writes reads right anchor value

theorem writeReadEq_of_eq (heap : Heap Address Value) (writes reads : Finset Address)
    {left right : Address} (same : left = right) : WriteReadEq heap writes reads left right := by
  subst right
  intro value anchor
  rfl

/-- Two real writes separate distinct live aliases. One of the two values must
differ from the anchor's old payload; no assumption about that old payload is
needed. This uses only the granted anchor read, not full heap visibility. -/
theorem writeReadEq_respects_identity (heap : Heap Address Value) (writes reads : Finset Address)
    (left right : Address) (leftLive : left ∈ heap.allocated) (rightLive : right ∈ heap.allocated)
    (leftWrite : left ∈ writes) (rightWrite : right ∈ writes) (leftRead : left ∈ reads)
    (first second : Value) (distinct : first ≠ second)
    (same : WriteReadEq heap writes reads left right) : left = right := by
  by_contra different
  have firstProbe := same first left
  have secondProbe := same second left
  rw [writeRead_same heap writes reads left first leftWrite leftRead leftLive,
    writeRead_other heap writes reads right left first rightWrite leftRead rightLive
      leftLive different] at firstProbe
  rw [writeRead_same heap writes reads left second leftWrite leftRead leftLive,
    writeRead_other heap writes reads right left second rightWrite leftRead rightLive
      leftLive different] at secondProbe
  exact distinct (Option.some.inj (firstProbe.trans secondProbe.symm))

/-- Full live-cell read/write visibility characterizes alias identity. A
restricted observer or a one-value payload type need not separate aliases. -/
theorem full_writeReadEq_iff [Nontrivial Value] (heap : Heap Address Value)
    (left right : Address) (leftLive : left ∈ heap.allocated) (rightLive : right ∈ heap.allocated) :
    WriteReadEq heap heap.allocated heap.allocated left right ↔ left = right := by
  constructor
  · intro same
    obtain ⟨first, second, distinct⟩ := exists_pair_ne Value
    exact writeReadEq_respects_identity heap _ _ left right leftLive rightLive leftLive rightLive
      leftLive first second distinct same
  · exact writeReadEq_of_eq heap _ _

/-- Any relation that licenses replacement in these actual admitted contexts
must respect identity on the live cells for which the contexts are available.
No claim is made about ungranted writes, reads or hidden references. -/
theorem substitutive_relation_respects_identity (heap : Heap Address Value)
    (writes reads : Finset Address) (relation : Address → Address → Prop)
    (licenses : ∀ left right, relation left right → WriteReadEq heap writes reads left right)
    (left right : Address) (leftLive : left ∈ heap.allocated) (rightLive : right ∈ heap.allocated)
    (leftWrite : left ∈ writes) (rightWrite : right ∈ writes) (leftRead : left ∈ reads)
    (first second : Value) (distinct : first ≠ second) (related : relation left right) :
    left = right :=
  writeReadEq_respects_identity heap writes reads left right leftLive rightLive leftWrite rightWrite
    leftRead first second distinct (licenses left right related)

/-- Rooted liveness supplies the allocation conditions of the conditional
identity-separation theorem; authority is still supplied separately. -/
theorem writeReadEq_respects_live_identity {Owner : Type uOwner}
    (heap : Heap Address Value) (roots : Roots Owner Address) (writes reads : Finset Address)
    (left right : Address) (leftLive : Live heap roots left) (rightLive : Live heap roots right)
    (leftWrite : left ∈ writes) (rightWrite : right ∈ writes) (leftRead : left ∈ reads)
    (first second : Value) (distinct : first ≠ second)
    (same : WriteReadEq heap writes reads left right) : left = right :=
  writeReadEq_respects_identity heap writes reads left right (live_allocated heap roots leftLive)
    (live_allocated heap roots rightLive) leftWrite rightWrite leftRead first second distinct same

/-! ### Three simultaneously available scalar policies

`identityCompare` has no heap argument. `payloadCompare` explicitly selects a
heap. Partially applying the latter to an immutable captured heap gives the
frozen policy; applying it to each selected current heap gives the live policy.
No ambient-world lookup is hidden in the pure comparator. These policies make
different promises on the same cells and are not mutually exclusive designs.
-/

def identityCompare (left right : Address) : Bool := decide (left = right)

theorem identityCompare_true_iff (left right : Address) :
    identityCompare left right = true ↔ left = right := by
  simp [identityCompare]

theorem identityCompare_refl (address : Address) : identityCompare address address = true := by
  simp [identityCompare]

theorem identityCompare_symm (left right : Address) :
    identityCompare left right = identityCompare right left := by
  simp only [identityCompare, eq_comm]

theorem identityCompare_trans {left middle right : Address}
    (first : identityCompare left middle = true) (second : identityCompare middle right = true) :
    identityCompare left right = true :=
  (identityCompare_true_iff left right).mpr
    (((identityCompare_true_iff left middle).mp first).trans
      ((identityCompare_true_iff middle right).mp second))

/-- Compare just the scalar payload observations in this explicit heap.
Absent/absent is an equal observation, not an assertion of live aliasing. -/
def payloadCompare [DecidableEq Value] (heap : Heap Address Value) (left right : Address) : Bool :=
  match heap.lookup left, heap.lookup right with
  | none, none => true
  | some first, some second => decide (first.value = second.value)
  | _, _ => false

omit [DecidableEq Address] in
theorem payloadCompare_true_iff [DecidableEq Value] (heap : Heap Address Value)
    (left right : Address) : payloadCompare heap left right = true ↔ PayloadEq heap left right := by
  cases leftFound : heap.lookup left <;> cases rightFound : heap.lookup right <;>
    simp [payloadCompare, PayloadEq, Heap.readPayload, leftFound, rightFound]

omit [DecidableEq Address] in
theorem payloadCompare_refl [DecidableEq Value] (heap : Heap Address Value) (address : Address) :
    payloadCompare heap address address = true :=
  (payloadCompare_true_iff heap address address).mpr rfl

omit [DecidableEq Address] in
theorem payloadCompare_symm [DecidableEq Value] (heap : Heap Address Value) (left right : Address) :
    payloadCompare heap left right = payloadCompare heap right left := by
  rw [Bool.eq_iff_iff, payloadCompare_true_iff, payloadCompare_true_iff]
  exact ⟨Eq.symm, Eq.symm⟩

omit [DecidableEq Address] in
theorem payloadCompare_trans [DecidableEq Value] (heap : Heap Address Value)
    {left middle right : Address} (first : payloadCompare heap left middle = true)
    (second : payloadCompare heap middle right = true) : payloadCompare heap left right = true :=
  (payloadCompare_true_iff heap left right).mpr
    (((payloadCompare_true_iff heap left middle).mp first).trans
      ((payloadCompare_true_iff heap middle right).mp second))

omit [DecidableEq Address] in
/-- Freezing the explicit heap selects a coherent fixed-world equivalence.
It does not turn a mutable host pointer into an immutable snapshot. -/
theorem frozen_payload_comparison_equivalence [DecidableEq Value] (snapshot : Heap Address Value) :
    Equivalence (fun left right => payloadCompare snapshot left right = true) := by
  exact ⟨payloadCompare_refl snapshot, fun same =>
    (payloadCompare_true_iff snapshot _ _).mpr
      ((payloadCompare_true_iff snapshot _ _).mp same).symm,
    fun first second => payloadCompare_trans snapshot first second⟩

theorem payloadCompare_write_outside [DecidableEq Value] (heap : Heap Address Value)
    (address : Address) (value : Value) (left right : Address)
    (leftOther : left ≠ address) (rightOther : right ≠ address) :
    payloadCompare (heap.writePayload address value) left right = payloadCompare heap left right := by
  rw [Bool.eq_iff_iff, payloadCompare_true_iff, payloadCompare_true_iff]
  exact payloadEq_write_outside heap address value left right leftOther rightOther

/-- Two independent writes realize the selected scalar values in an actual
reference-closed heap. This derives the observation from mutation/read laws. -/
theorem payloadEq_after_independent_writes (heap : Heap Address Value)
    (left right : Address) (leftLive : left ∈ heap.allocated) (rightLive : right ∈ heap.allocated)
    (different : left ≠ right) (first second : Value) :
    PayloadEq ((heap.writePayload left first).writePayload right second) left right ↔
      first = second := by
  unfold PayloadEq
  rw [Heap.readPayload_write_other (heap.writePayload left first) right left second different,
    Heap.readPayload_write_same heap left first leftLive,
    Heap.readPayload_write_same (heap.writePayload left first) right second rightLive]
  exact ⟨Option.some.inj, congrArg some⟩

/-- A world-independent pure comparator cannot agree with live scalar equality
through all values of an independently writable cell. Two actual reachable
heaps already contradict that promise. An explicitly heap-indexed comparator
or a fixed snapshot comparator has no such conflicting requirement. -/
theorem no_fixed_comparator_tracks_independent_write_worlds (heap : Heap Address Value)
    (left right : Address) (leftLive : left ∈ heap.allocated) (rightLive : right ∈ heap.allocated)
    (different : left ≠ right) (first second : Value) (distinct : first ≠ second) :
    ¬ ∃ compare : Address → Address → Bool, ∀ current : Value,
      (compare left right = true ↔
        PayloadEq ((heap.writePayload left first).writePayload right current) left right) := by
  rintro ⟨compare, accurate⟩
  have equalWorld := (payloadEq_after_independent_writes heap left right leftLive rightLive
    different first first).mpr rfl
  have equalAnswer := (accurate first).mpr equalWorld
  have unequalWorld := (accurate second).mp equalAnswer
  exact distinct ((payloadEq_after_independent_writes heap left right leftLive rightLive
    different first second).mp unequalWorld)

end MutableObservation

section WriteRelocation

universe uDestinationValue

variable {DestinationAddress : Type} {DestinationValue : Type uDestinationValue}
variable [DecidableEq DestinationAddress]

omit [DecidableEq Address] in
/-- Scalar readout follows the payload interpretation, while the address map
continues to name the actual resource. Payload interpretation need not be
injective. -/
theorem Relocation.readPayload {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (address : Address) :
    destination.readPayload (copy.address address) =
      (source.readPayload address).map copy.payload := by
  simp only [Heap.readPayload, copy.lookup_eq, Option.map_map]
  rfl

/-- Transport the actual payload mutation. The resulting relocation is
constructed from the original lookups and address injectivity; post-write
lookup agreement is not assumed. -/
def Relocation.writePayload {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (address : Address) (value : Value) :
    Relocation (source.writePayload address value)
      (destination.writePayload (copy.address address) (copy.payload value)) where
  address := copy.address
  payload := copy.payload
  injective := copy.injective
  lookup_eq query := by
    by_cases same : query = address
    · subst query
      rw [Heap.writePayload_lookup_same, copy.lookup_eq, Heap.writePayload_lookup_same]
      cases source.lookup address <;> rfl
    · rw [Heap.writePayload_lookup_other destination (copy.address address) (copy.address query)
        (copy.payload value) (fun equal => same (copy.injective equal)),
        copy.lookup_eq, Heap.writePayload_lookup_other source address query value same]

/-- Write/read probes commute with complete resource relocation. The law is
about transported addresses in independent heaps, not mixed raw/copy aliases. -/
theorem Relocation.write_readPayload {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (hole anchor : Address) (value : Value) :
    (destination.writePayload (copy.address hole) (copy.payload value)).readPayload
        (copy.address anchor) =
      ((source.writePayload hole value).readPayload anchor).map copy.payload :=
  (copy.writePayload hole value).readPayload anchor

/-- The constructed post-write relocation preserves and reflects arbitrary
successful path aliases, including repeated and cyclic paths. -/
theorem Relocation.write_aliases_iff {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (hole : Address) (value : Value)
    (leftStart rightStart : Address) (left right : List Address) :
    Aliases (destination.writePayload (copy.address hole) (copy.payload value))
        (copy.address leftStart) (left.map copy.address)
        (copy.address rightStart) (right.map copy.address) ↔
      Aliases (source.writePayload hole value) leftStart left rightStart right :=
  (copy.writePayload hole value).aliases_iff leftStart rightStart left right

omit [DecidableEq Address] in
/-- Relocation reflects alias identity independently of whether distinct
payload values are collapsed by the representation map. -/
theorem Relocation.address_eq_iff {source : Heap Address Value}
    {destination : Heap DestinationAddress DestinationValue}
    (copy : Relocation source destination) (left right : Address) :
    copy.address left = copy.address right ↔ left = right :=
  copy.injective.eq_iff

end WriteRelocation

namespace MutableObservation.Controls

/-- Equal scalar cells with distinct resource identities. -/
def pairHeap : Heap (Fin 2) Nat where
  lookup _ := some ⟨7, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

theorem equal_scalars_are_distinct_live_resources :
    PayloadEq pairHeap 0 1 ∧ (0 : Fin 2) ≠ 1 ∧
      0 ∈ pairHeap.allocated ∧ 1 ∈ pairHeap.allocated := by decide

/-- Both observations return real values. The two write-hole substitutions
give different results although the untouched payloads were equal. -/
theorem equal_scalars_fail_write_substitution :
    writeRead pairHeap pairHeap.allocated pairHeap.allocated 0 0 9 = some 9 ∧
      writeRead pairHeap pairHeap.allocated pairHeap.allocated 1 0 9 = some 7 ∧
      ¬ WriteReadEq pairHeap pairHeap.allocated pairHeap.allocated 0 1 := by
  refine ⟨by decide, by decide, ?_⟩
  intro same
  exact (by decide : (0 : Fin 2) ≠ 1)
    ((full_writeReadEq_iff pairHeap 0 1 (by decide) (by decide)).mp same)

theorem actual_two_value_probes_force_identity (left right : Fin 2)
    (same : WriteReadEq pairHeap pairHeap.allocated pairHeap.allocated left right) : left = right :=
  writeReadEq_respects_identity pairHeap _ _ left right (by simp [pairHeap])
    (by simp [pairHeap]) (by simp [pairHeap]) (by simp [pairHeap]) (by simp [pairHeap])
    7 9 (by decide) same

theorem same_reference_passes_all_write_read_probes (address : Fin 2) :
    WriteReadEq pairHeap pairHeap.allocated pairHeap.allocated address address :=
  writeReadEq_of_eq pairHeap _ _ rfl

/-- Changing the selected world can invalidate scalar equality even though
the addresses and their alias relation did not change. -/
theorem world_change_invalidates_value_equality :
    PayloadEq pairHeap 0 1 ∧ ¬ PayloadEq (pairHeap.writePayload 0 9) 0 1 ∧
      (pairHeap.writePayload 0 9).readPayload 0 = some 9 ∧
      pairHeap.readPayload 0 = some 7 ∧
      Aliases (pairHeap.writePayload 0 9) 0 [] 0 [] := by
  unfold Aliases
  decide

theorem mutation_retains_allocation_references_and_bytes :
    (pairHeap.writePayload 0 9).allocated = pairHeap.allocated ∧
      (pairHeap.writePayload 0 9).dependencies 0 = pairHeap.dependencies 0 ∧
      ((pairHeap.writePayload 0 9).lookup 0).map Cell.bytes =
        (pairHeap.lookup 0).map Cell.bytes := by
  exact ⟨rfl, Heap.writePayload_dependencies pairHeap 0 0 9,
    Heap.writePayload_bytes pairHeap 0 0 9⟩

def pairRoots : Roots Unit (Fin 2) := {((), 0), ((), 1)}

theorem actual_live_roots_supply_separating_context (left right : Fin 2)
    (same : WriteReadEq pairHeap pairHeap.allocated pairHeap.allocated left right) :
    Live (pairHeap.writePayload 0 9) pairRoots left ∧ left = right := by
  have allocated : left ∈ pairHeap.allocated := by simp [pairHeap]
  have rooted : ((), left) ∈ pairRoots := by
    have alternatives : left = 0 ∨ left = 1 := by omega
    rcases alternatives with rfl | rfl <;> decide
  have leftLive := live_of_root pairHeap pairRoots rooted allocated
  refine ⟨(Heap.writePayload_live_iff pairHeap pairRoots 0 9 left).mpr leftLive, ?_⟩
  have rightRooted : ((), right) ∈ pairRoots := by
    have alternatives : right = 0 ∨ right = 1 := by omega
    rcases alternatives with rfl | rfl <;> decide
  exact writeReadEq_respects_live_identity pairHeap pairRoots _ _ left right leftLive
    (live_of_root pairHeap pairRoots rightRooted (by simp [pairHeap])) allocated
    (by simp [pairHeap]) allocated 7 9 (by decide) same

def threeHeap : Heap (Fin 3) Nat where
  lookup _ := some ⟨7, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

/-- A restricted observer performs successful writes and reads, but cannot
inspect either written alias. Such an observer cannot establish identity. -/
theorem restricted_read_observer_does_not_separate_identity :
    WriteReadEq threeHeap {0, 1} {2} 0 1 ∧ (0 : Fin 3) ≠ 1 ∧
      writeRead threeHeap {0, 1} {2} 0 2 9 = some 7 ∧
      writeRead threeHeap {0, 1} {2} 1 2 9 = some 7 := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro value anchor
  have alternatives : anchor = 0 ∨ anchor = 1 ∨ anchor = 2 := by omega
  rcases alternatives with rfl | rfl | rfl <;>
    simp [writeRead, Heap.readPayload, Heap.writePayload, threeHeap]

/-- Outside the actual observed support, scalar writes preserve a cached
ordered readout, with duplicate observations retained. -/
theorem writes_outside_duplicate_read_support_preserve_readout :
    [1, 2, 1].map (threeHeap.writePayload 0 9).readPayload =
      [1, 2, 1].map threeHeap.readPayload :=
  Heap.readPayload_list_write_outside threeHeap 0 9 [1, 2, 1] (by decide)

theorem unobserved_write_preserves_value_relation :
    PayloadEq (threeHeap.writePayload 0 9) 1 2 ↔ PayloadEq threeHeap 1 2 :=
  payloadEq_write_outside threeHeap 0 9 1 2 (by decide) (by decide)

/-- Frozen readouts may coherently identify equal values without identifying
the live mutable resources that produced them. -/
theorem frozen_scalar_readouts_are_coherent :
    (pairHeap.readPayload 0).map (fun value => value + 1) = some 8 ∧
      (pairHeap.readPayload 1).map (fun value => value + 1) = some 8 ∧
      ¬ WriteReadEq pairHeap pairHeap.allocated pairHeap.allocated 0 1 := by
  exact ⟨by decide, by decide, equal_scalars_fail_write_substitution.2.2⟩

/-- A single possible payload value cannot implement the two-value probe. -/
def unitHeap : Heap (Fin 2) Unit where
  lookup _ := some ⟨(), ∅, 8⟩
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

theorem one_value_payload_cannot_separate_identity :
    WriteReadEq unitHeap unitHeap.allocated unitHeap.allocated 0 1 ∧ (0 : Fin 2) ≠ 1 := by
  refine ⟨?_, by decide⟩
  intro value anchor
  cases value
  have alternatives : anchor = 0 ∨ anchor = 1 := by omega
  rcases alternatives with rfl | rfl <;> decide

def cyclicCell (address : Fin 2) : Cell (Fin 2) Nat :=
  ⟨7, {if address = 0 then 1 else 0}, 8⟩

def cyclicHeap : Heap (Fin 2) Nat where
  lookup address := some (cyclicCell address)
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

theorem scalar_write_preserves_cyclic_path_aliases :
    Aliases (cyclicHeap.writePayload 0 9) 0 [1, 0, 1] 1 [] ∧
      (cyclicHeap.writePayload 0 9).readPayload 0 ≠ cyclicHeap.readPayload 0 := by
  unfold Aliases
  decide

/-- The isolated copy occupies fresh addresses beside retained source cells. -/
def copyHeap : Heap (Fin 4) Nat where
  lookup _ := some ⟨7, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

def copyAddress (address : Fin 2) : Fin 4 := ⟨address.val + 2, by omega⟩

def freshCopy : Relocation pairHeap copyHeap where
  address := copyAddress
  payload := id
  injective := by
    intro left right same
    apply Fin.ext
    have values := congrArg Fin.val same
    change left.val + 2 = right.val + 2 at values
    omega
  lookup_eq := by decide +kernel

theorem fresh_clone_preserves_internal_alias_but_is_not_cached_source :
    Aliases copyHeap (freshCopy.address 0) [] (freshCopy.address 0) [] ∧
      ¬ Aliases copyHeap (freshCopy.address 0) [] 0 [] ∧
      copyHeap.readPayload (freshCopy.address 0) = copyHeap.readPayload 0 := by
  unfold Aliases
  decide

theorem clone_write_does_not_mutate_retained_source :
    (copyHeap.writePayload (freshCopy.address 0) 9).readPayload (freshCopy.address 0) = some 9 ∧
      (copyHeap.writePayload (freshCopy.address 0) 9).readPayload 0 = some 7 := by decide

theorem actual_relocated_write_read :
    (copyHeap.writePayload (freshCopy.address 0) 9).readPayload (freshCopy.address 0) =
      (pairHeap.writePayload 0 9).readPayload 0 :=
  freshCopy.write_readPayload 0 0 9

theorem cyclic_relocation_and_write_preserve_actual_alias :
    Aliases
      (Mettapedia.Machines.ResourceOwnership.Examples.copiedHeap.writePayload
        (Mettapedia.Machines.ResourceOwnership.Examples.shiftedCopy.address 0) (7 + 100))
      (Mettapedia.Machines.ResourceOwnership.Examples.shiftedCopy.address 0)
      ([1, 2].map Mettapedia.Machines.ResourceOwnership.Examples.shiftedCopy.address)
      (Mettapedia.Machines.ResourceOwnership.Examples.shiftedCopy.address 2) [] := by
  apply (Mettapedia.Machines.ResourceOwnership.Examples.shiftedCopy.write_aliases_iff 0 7 0 2 [1, 2] []).mpr
  exact (aliases_writePayload Mettapedia.Machines.ResourceOwnership.Examples.cyclicHeap 0 7 0 2 [1, 2] []).mpr
    Mettapedia.Machines.ResourceOwnership.Examples.two_paths_share_cyclic_endpoint

def distinctHeap : Heap (Fin 2) Nat where
  lookup address := some ⟨address.val, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff _ := by simp
  closed _ _ _ next _ := Finset.mem_univ next

/-- A noninjective payload interpretation is a valid relocation; address
injectivity and mutation alias identity remain separate obligations. -/
def collapsedPayloadCopy : Relocation distinctHeap copyHeap where
  address := copyAddress
  payload _ := 7
  injective := freshCopy.injective
  lookup_eq := by decide +kernel

theorem payload_collapse_does_not_collapse_resource_identity :
    distinctHeap.readPayload 0 ≠ distinctHeap.readPayload 1 ∧
      PayloadEq copyHeap (collapsedPayloadCopy.address 0) (collapsedPayloadCopy.address 1) ∧
      collapsedPayloadCopy.address 0 ≠ collapsedPayloadCopy.address 1 ∧
      ¬ Aliases copyHeap (collapsedPayloadCopy.address 0) []
        (collapsedPayloadCopy.address 1) [] := by
  unfold Aliases
  decide

theorem identity_transport_preserves_same_reference :
    (Relocation.ofEquiv pairHeap (Equiv.refl (Fin 2)) id).address 0 = 0 ∧
      (pairHeap.relabel (Equiv.refl (Fin 2)) id).readPayload 0 = pairHeap.readPayload 0 ∧
      Aliases (pairHeap.relabel (Equiv.refl (Fin 2)) id) 0 [] 0 [] := by
  unfold Aliases
  decide

def originalRegion : RequestBorrow.Region Nat (Fin 2) Nat := ⟨⟨3, 5⟩, pairHeap⟩

def originalView : RequestBorrow.View Nat (Fin 2) := ⟨originalRegion.stamp, [(0, [])]⟩

/-- Capture an actual pure comparison closure at the original immutable heap.
Future current-world writes do not change this selected snapshot policy. -/
def frozenComparison : Fin 2 → Fin 2 → Bool := payloadCompare originalRegion.heap

theorem three_policies_coexist_on_the_same_heap :
    identityCompare (0 : Fin 2) 1 = false ∧
      payloadCompare pairHeap 0 1 = true ∧ frozenComparison 0 1 = true ∧
      payloadCompare (pairHeap.writePayload 0 9) 0 1 = false ∧
      identityCompare (0 : Fin 2) 0 = true ∧ frozenComparison 0 1 = true := by decide

theorem live_comparator_tracks_explicit_written_world (leftValue rightValue : Nat) :
    payloadCompare ((pairHeap.writePayload 0 leftValue).writePayload 1 rightValue) 0 1 = true ↔
      leftValue = rightValue := by
  rw [payloadCompare_true_iff]
  exact payloadEq_after_independent_writes pairHeap 0 1 (by decide) (by decide) (by decide)
    leftValue rightValue

theorem frozen_policy_is_equivalence_with_distinct_equal_cells :
    Equivalence (fun left right => frozenComparison left right = true) ∧
      frozenComparison 0 1 = true ∧ (0 : Fin 2) ≠ 1 := by
  exact ⟨frozen_payload_comparison_equivalence originalRegion.heap, by decide, by decide⟩

theorem frozen_policy_does_not_promise_current_world_accuracy :
    frozenComparison 0 1 = true ∧
      ¬ PayloadEq (pairHeap.writePayload 0 9) 0 1 ∧
      PayloadEq originalRegion.heap 0 1 := by decide

theorem no_single_fixed_comparator_tracks_all_current_heaps :
    ¬ ∃ compare : Fin 2 → Fin 2 → Bool, ∀ current : Heap (Fin 2) Nat,
      (compare 0 1 = true ↔ PayloadEq current 0 1) := by
  rintro ⟨compare, accurate⟩
  apply no_fixed_comparator_tracks_independent_write_worlds pairHeap 0 1
    (by decide) (by decide) (by decide) 7 9 (by decide)
  exact ⟨compare, fun current => accurate _⟩

theorem identity_policy_is_stable_across_payload_worlds (value : Nat) :
    identityCompare (0 : Fin 2) 1 = false ∧
      Aliases (pairHeap.writePayload 0 value) 0 [] 0 [] ∧
      ¬ Aliases (pairHeap.writePayload 0 value) 0 [] 1 [] := by
  refine ⟨by decide, ?_, ?_⟩
  · exact (aliases_writePayload pairHeap 0 value 0 0 [] []).mpr (by unfold Aliases; decide)
  · rw [aliases_writePayload]
    unfold Aliases
    decide

theorem equal_contents_do_not_imply_same_generation :
    originalRegion.heap.readPayload 0 =
      (RequestBorrow.reset originalRegion pairHeap).heap.readPayload 0 ∧
      originalRegion.stamp ≠ (RequestBorrow.reset originalRegion pairHeap).stamp ∧
      RequestBorrow.read (RequestBorrow.reset originalRegion pairHeap) originalView = none := by
  exact ⟨rfl, by decide,
    RequestBorrow.read_reset_rejected originalRegion pairHeap originalView rfl⟩

theorem equal_contents_do_not_imply_same_origin :
    originalRegion.heap.readPayload 0 =
      (RequestBorrow.Region.mk ⟨4, 5⟩ pairHeap).heap.readPayload 0 ∧
      RequestBorrow.read (RequestBorrow.Region.mk ⟨4, 5⟩ pairHeap) originalView = none := by decide

def lifetimeState : AcquiredUse.State Nat Nat Nat :=
  ⟨true, {0}, {1}, none, some 7⟩

def exclusiveState : AcquiredUse.State Nat Nat Nat :=
  ⟨true, {0}, {1}, some 1, some 7⟩

/-- Both states are obtained through actual use acquisition and expose the
same payload. Only the separately issued exclusive use grants mutation. -/
theorem equal_contents_do_not_imply_mutation_authority :
    AcquiredUse.acquire 1 .lifetime 0 1 (AcquiredUse.initial 0 7) =
        some ⟨lifetimeState, none⟩ ∧
      AcquiredUse.acquire 1 .exclusive 0 1 (AcquiredUse.initial 0 7) =
        some ⟨exclusiveState, none⟩ ∧
      AcquiredUse.readUse 1 lifetimeState = AcquiredUse.readUse 1 exclusiveState ∧
      ¬ AcquiredUse.mayMutate 1 lifetimeState ∧ AcquiredUse.mayMutate 1 exclusiveState := by decide

end MutableObservation.Controls

end Mettapedia.Machines.ResourceOwnership

/-!
## Finite ordered descriptor observations

Ordinal paths use the existing adaptive read-only query program. Its replies
are complete optional cell headers and ordered slot lists. The executed log
retains repeated reads, negative lookups and the selected slot order. Scalar
writes preserve topology; query replay follows from agreement on actual reads.

The returned payload is the opaque `Cell.value`, not recursive State equality.
The node-reply count does not price slot lookup, descriptor construction,
allocation or native validation. Native current-view, canonical identity,
lifetime, authority and refusal interpretation remain instance obligations.
-/

namespace Mettapedia.Machines.ResourceOwnership.OrderedObservation

universe u
variable {A : Type} {V : Type u}

/-- An ordinal path is interpreted by the existing adaptive query program.
Each actual reply includes both the optional header and its ordered slots. -/
def program (start : A) : List Nat →
    ReadOnlyQuery.Program A (DescriptorAdmission.Descriptor A V) (Option (A × Cell A V))
  | [] => .read start fun reply => .pure (reply.1.map (start, ·))
  | index :: rest => .read start fun reply =>
      match reply.1 with
      | none => .pure none
      | some _ => match reply.2[index]? with
        | none => .pure none
        | some child => program child rest

def provider (heap : Heap A V) (slots : A → List A) (address : A) :
    DescriptorAdmission.Descriptor A V := (heap.lookup address, slots address)

def observe (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) :=
  ReadOnlyQuery.run (provider heap slots) (program start path)

def result (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) :=
  (observe heap slots start path).answer

def target (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) :=
  (result heap slots start path).map Prod.fst

def payload (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) :=
  (result heap slots start path).map (fun found => found.2.value)

@[simp] theorem result_nil (heap : Heap A V) (slots : A → List A) (start : A) :
    result heap slots start [] = (heap.lookup start).map (start, ·) := rfl

@[simp] theorem result_cons (heap : Heap A V) (slots : A → List A)
    (start : A) (index : Nat) (rest : List Nat) :
    result heap slots start (index :: rest) =
      (heap.lookup start).bind (fun _ =>
        (slots start)[index]?.bind (fun child => result heap slots child rest)) := by
  cases h : heap.lookup start <;>
    simp [result, observe, ReadOnlyQuery.run, program, provider, h]
  cases s : (slots start)[index]? <;> simp [ReadOnlyQuery.run]

theorem result_lookup (heap : Heap A V) (slots : A → List A) (start end_ : A)
    (path : List Nat) (cell : Cell A V) (found : result heap slots start path = some (end_, cell)) :
    heap.lookup end_ = some cell := by
  induction path generalizing start with
  | nil =>
      obtain ⟨original, atStart, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      exact atStart
  | cons index rest ih =>
      rw [result_cons] at found
      obtain ⟨_, _, found⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨child, _, found⟩ := Option.bind_eq_some_iff.mp found
      exact ih child found

theorem reads_nonempty (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) :
    (observe heap slots start path).reads ≠ [] := by
  cases path <;> simp [observe, program, ReadOnlyQuery.run]

theorem read_count (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) :
    (observe heap slots start path).reads.length ≤ path.length + 1 := by
  induction path generalizing start with
  | nil => simp [observe, program, ReadOnlyQuery.run]
  | cons index rest ih =>
      cases h : heap.lookup start with
      | none => simp [observe, program, ReadOnlyQuery.run, provider, h]
      | some cell =>
          cases s : (slots start)[index]? with
          | none => simp [observe, program, ReadOnlyQuery.run, provider, h, s]
          | some child =>
              simpa [observe, program, ReadOnlyQuery.run, provider, h, s] using
                Nat.add_le_add_right (ih child) 1

/-- A finite path around a self-cycle repeats actual reads rather than
deduplicating the request log or unfolding an infinite tree. -/
theorem self_cycle_reads (heap : Heap A V) (slots : A → List A) (root : A)
    (cell : Cell A V) (header : heap.lookup root = some cell)
    (backedge : (slots root)[0]? = some root) (length : Nat) :
    observe heap slots root (List.replicate length 0) =
      ⟨some (root, cell), List.replicate (length + 1) (root, provider heap slots root)⟩ := by
  induction length with
  | zero => simp [observe, program, ReadOnlyQuery.run, provider, header]
  | succ length ih =>
      have extended := congrArg (fun observed : ReadOnlyQuery.Observation A
          (DescriptorAdmission.Descriptor A V) (Option (A × Cell A V)) =>
        (⟨observed.answer, (root, provider heap slots root) :: observed.reads⟩ :
          ReadOnlyQuery.Observation A (DescriptorAdmission.Descriptor A V) (Option (A × Cell A V)))) ih
      simpa only [observe, List.replicate_succ, program, ReadOnlyQuery.run,
        provider, header, backedge] using extended

variable [DecidableEq A]

/-- Every successful ordinal query realizes an actual existing heap walk.
The returned itinerary is extracted from its executed read log; cycles retain
their repeated occurrences. Ordered-slot support is an explicit hypothesis. -/
theorem successful_walk (heap : Heap A V) (slots : A → List A)
    (exactSlots : ∀ a, (slots a).toFinset = heap.dependencies a)
    (start end_ : A) (path : List Nat) (cell : Cell A V)
    (found : result heap slots start path = some (end_, cell)) :
    ∃ word : List A, (observe heap slots start path).reads.map Prod.fst = start :: word ∧
      word.length = path.length ∧ walk heap start word = some (end_, cell) := by
  induction path generalizing start with
  | nil =>
      obtain ⟨original, atStart, equal⟩ := Option.map_eq_some_iff.mp found
      cases equal
      change heap.lookup end_ = some cell at atStart
      exact ⟨[], rfl, rfl, by simp [walk, atStart]⟩
  | cons index rest ih =>
      rw [result_cons] at found
      obtain ⟨header, atStart, remaining⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨child, atSlot, remaining⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨word, logged, length, walked⟩ := ih child remaining
      have member : child ∈ header.references := by
        have inside : child ∈ (slots start).toFinset :=
          List.mem_toFinset.mpr (List.mem_of_getElem? atSlot)
        rw [exactSlots start] at inside
        simpa [Heap.dependencies, atStart] using inside
      refine ⟨child :: word, ?_, by simp [length], ?_⟩
      · simpa [observe, program, ReadOnlyQuery.run, provider, atStart, atSlot] using
          congrArg (List.cons start) logged
      · simp [walk, atStart, member, walked]

theorem successful_read_count (heap : Heap A V) (slots : A → List A)
    (exactSlots : ∀ a, (slots a).toFinset = heap.dependencies a)
    (start end_ : A) (path : List Nat) (cell : Cell A V)
    (found : result heap slots start path = some (end_, cell)) :
    (observe heap slots start path).reads.length = path.length + 1 := by
  obtain ⟨word, logged, length, _⟩ := successful_walk heap slots exactSlots start end_ path cell found
  have count := congrArg List.length logged
  simpa only [List.length_map, List.length_cons, length] using count

omit [DecidableEq A] in
theorem target_allocated (heap : Heap A V) (slots : A → List A)
    (start end_ : A) (path : List Nat) (found : target heap slots start path = some end_) :
    end_ ∈ heap.allocated := by
  obtain ⟨pair, answered, equal⟩ := Option.map_eq_some_iff.mp found
  cases equal
  exact (heap.allocated_iff pair.1).mpr ⟨pair.2, result_lookup heap slots start pair.1 path pair.2 answered⟩

/-- Updating an unconsulted cell preserves the actual full reply log as well
as the result, by the existing query replay theorem. -/
theorem write_outside_reads (heap : Heap A V) (slots : A → List A)
    (start address : A) (path : List Nat) (value : V)
    (outside : address ∉ (observe heap slots start path).reads.map Prod.fst) :
    observe (heap.writePayload address value) slots start path =
      observe heap slots start path := by
  apply ReadOnlyQuery.run_eq_of_agrees
  intro reply member
  have different : reply.1 ≠ address := by
    intro equal
    apply outside
    exact equal ▸ List.mem_map_of_mem member
  have old := ReadOnlyQuery.run_agrees (provider heap slots) (program start path) reply member
  rw [← old]
  simp only [provider, Heap.writePayload_lookup_other heap address reply.1 value different]

/-- Writes preserve all path choices and alter only the final cell payload. -/
theorem result_write (heap : Heap A V) (slots : A → List A) (start address : A)
    (path : List Nat) (value : V) :
    result (heap.writePayload address value) slots start path =
      (result heap slots start path).map (fun found =>
        (found.1, if found.1 = address then { found.2 with value := value } else found.2)) := by
  induction path generalizing start with
  | nil =>
      by_cases same : start = address
      · subst start
        cases h : heap.lookup address <;> simp [h]
      · rw [result_nil, Heap.writePayload_lookup_other heap address start value same]
        cases h : heap.lookup start <;> simp [h, same]
  | cons index rest ih =>
      rw [result_cons, result_cons]
      by_cases same : start = address
      · subst start
        cases h : heap.lookup address <;> simp only [Heap.writePayload_lookup_same, h,
          Option.map_none, Option.bind_none, Option.map_some, Option.bind_some]
        cases s : (slots address)[index]? <;> simp [ih]
      · rw [Heap.writePayload_lookup_other heap address start value same]
        cases h : heap.lookup start <;> simp only [Option.bind_none, Option.map_none,
          Option.bind_some]
        cases s : (slots start)[index]? <;> simp [ih]

@[simp] theorem target_write (heap : Heap A V) (slots : A → List A)
    (start address : A) (path : List Nat) (value : V) :
    target (heap.writePayload address value) slots start path = target heap slots start path := by
  rw [target, result_write]
  cases h : result heap slots start path <;> simp [target, h]

theorem payload_write (heap : Heap A V) (slots : A → List A)
    (start address : A) (path : List Nat) (value : V) :
    payload (heap.writePayload address value) slots start path =
      if target heap slots start path = some address then some value else
        payload heap slots start path := by
  rw [payload, result_write]
  cases h : result heap slots start path with
  | none => simp [target, payload, h]
  | some found =>
      by_cases same : found.1 = address <;> simp [target, payload, h, same]

/-- Invalid ordinal writes are explicit no-ops. They are not service refusal. -/
def write (heap : Heap A V) (slots : A → List A) (start : A) (path : List Nat) (value : V) :
    Heap A V :=
  match target heap slots start path with
  | none => heap
  | some address => heap.writePayload address value

/-- Two failed paths do not alias. Only a common allocated endpoint counts. -/
def impact (heap : Heap A V) (slots : A → List A) (start : A)
    (written read : List Nat) : Bool :=
  match target heap slots start written, target heap slots start read with
  | some left, some right => decide (left = right)
  | _, _ => false

@[simp] theorem target_after_write (heap : Heap A V) (slots : A → List A)
    (start : A) (written read : List Nat) (value : V) :
    target (write heap slots start written value) slots start read =
      target heap slots start read := by
  unfold write
  split <;> simp

@[simp] theorem impact_after_write (heap : Heap A V) (slots : A → List A)
    (start : A) (written left right : List Nat) (value : V) :
    impact (write heap slots start written value) slots start left right =
      impact heap slots start left right := by
  simp [impact]

/-- The actual write/read law exposes precisely the alias incidence needed
by the observer, without adding an otherwise invisible validity bit. -/
theorem payload_after_write (heap : Heap A V) (slots : A → List A)
    (start : A) (written read : List Nat) (value : V) :
    payload (write heap slots start written value) slots start read =
      if impact heap slots start written read then some value else
        payload heap slots start read := by
  unfold write impact
  cases w : target heap slots start written with
  | none => simp
  | some address =>
      rw [payload_write]
      cases r : target heap slots start read with
      | none => simp
      | some other =>
          by_cases same : address = other <;> simp [same, eq_comm]

omit [DecidableEq A] in
/-- Reference-set relocation alone forgets slot order. This additional
ordered transport premise permits the actual query to follow copied slots. -/
theorem result_relocation {B : Type} {W : Type} [DecidableEq B]
    {old : Heap A V} {new : Heap B W} (copy : Relocation old new)
    (oldSlots : A → List A) (newSlots : B → List B)
    (ordered : ∀ a, newSlots (copy.address a) = (oldSlots a).map copy.address)
    (start : A) (path : List Nat) :
    result new newSlots (copy.address start) path =
      (result old oldSlots start path).map (fun found =>
        (copy.address found.1, found.2.relocate copy.address copy.payload)) := by
  induction path generalizing start with
  | nil =>
      rw [result_nil, copy.lookup_eq, result_nil]
      cases h : old.lookup start <;> rfl
  | cons index rest ih =>
      rw [result_cons, result_cons, copy.lookup_eq, ordered start]
      cases h : old.lookup start <;> simp only [Option.map_none, Option.bind_none,
        Option.map_some, Option.bind_some]
      rw [List.getElem?_map]
      cases s : (oldSlots start)[index]? <;> simp [ih]

omit [DecidableEq A] in
theorem target_relocation {B : Type} {W : Type} [DecidableEq B]
    {old : Heap A V} {new : Heap B W} (copy : Relocation old new)
    (oldSlots : A → List A) (newSlots : B → List B)
    (ordered : ∀ a, newSlots (copy.address a) = (oldSlots a).map copy.address)
    (start : A) (path : List Nat) :
    target new newSlots (copy.address start) path =
      (target old oldSlots start path).map copy.address := by
  rw [target, result_relocation copy oldSlots newSlots ordered]
  cases h : result old oldSlots start path <;> simp [target, h]

omit [DecidableEq A] in
theorem payload_relocation {B : Type} {W : Type} [DecidableEq B]
    {old : Heap A V} {new : Heap B W} (copy : Relocation old new)
    (oldSlots : A → List A) (newSlots : B → List B)
    (ordered : ∀ a, newSlots (copy.address a) = (oldSlots a).map copy.address)
    (start : A) (path : List Nat) :
    payload new newSlots (copy.address start) path =
      (payload old oldSlots start path).map copy.payload := by
  rw [payload, result_relocation copy oldSlots newSlots ordered]
  cases h : result old oldSlots start path <;> simp [payload, Cell.relocate, h]

/-- Ordered queries inherit alias preservation from the existing injective
relocation. Equality of copied scalar values alone would not imply this. -/
theorem incidence_relocation {B : Type} {W : Type} [DecidableEq B]
    {old : Heap A V} {new : Heap B W} (copy : Relocation old new)
    (oldSlots : A → List A) (newSlots : B → List B)
    (ordered : ∀ a, newSlots (copy.address a) = (oldSlots a).map copy.address)
    (start : A) (written observed : List Nat) :
    impact new newSlots (copy.address start) written observed =
      impact old oldSlots start written observed := by
  simp only [impact, target_relocation copy oldSlots newSlots ordered]
  cases left : target old oldSlots start written <;>
    cases right : target old oldSlots start observed <;>
      simp [copy.injective.eq_iff]

end Mettapedia.Machines.ResourceOwnership.OrderedObservation

/-! A tracing collector can reclaim an unreachable cycle. An owner that only
releases objects when their strong reference counts reach zero has a different
obligation: introducing one strong edge must not close a directed path back to
its source. These results concern an explicitly supplied strong-edge relation;
they do not claim that a runtime's storage census enumerates that relation. -/

namespace Mettapedia.Machines.ResourceOwnership.StrongEdges

variable {Owner : Type}

/-- Add one owning edge to the existing directed ownership relation. -/
def add (edge : Owner → Owner → Prop) (source target : Owner) : Owner → Owner → Prop :=
  fun x y => edge x y ∨ (x = source ∧ y = target)

/-- There is no nonempty directed cycle of strong ownership. -/
def Acyclic (edge : Owner → Owner → Prop) : Prop :=
  ∀ x, ¬ Relation.TransGen edge x x

/-- A path after adding one edge is either an old nonempty path, or passes
from its start to the new edge and from that edge to its end using old edges.
Repeated uses of the added edge can be removed from such a witness. -/
theorem path_after_add {edge : Owner → Owner → Prop} {source target x y : Owner}
    (path : Relation.TransGen (add edge source target) x y) :
    Relation.TransGen edge x y ∨
      (Relation.ReflTransGen edge x source ∧ Relation.ReflTransGen edge target y) := by
  induction path with
  | single step =>
      rcases step with old | ⟨rfl, rfl⟩
      · exact Or.inl (.single old)
      · exact Or.inr ⟨.refl, .refl⟩
  | tail previous step ih =>
      rcases step with old | ⟨rfl, rfl⟩
      · rcases ih with oldPath | ⟨before, after⟩
        · exact Or.inl (oldPath.tail old)
        · exact Or.inr ⟨before, after.tail old⟩
      · rcases ih with oldPath | ⟨before, _⟩
        · exact Or.inr ⟨oldPath.to_reflTransGen, .refl⟩
        · exact Or.inr ⟨before, .refl⟩

/-- On an acyclic strong-owner graph, inserting one edge preserves acyclicity
exactly when its target cannot already reach its source. The reflexive path
also rejects a new self-edge. -/
theorem add_acyclic_iff {edge : Owner → Owner → Prop} {source target : Owner}
    (acyclic : Acyclic edge) :
    Acyclic (add edge source target) ↔
      ¬ Relation.ReflTransGen edge target source := by
  constructor
  · intro safe back
    have old : Relation.ReflTransGen (add edge source target) target source :=
      Relation.ReflTransGen.mono (r := edge) (p := add edge source target)
        (fun _ _ step => Or.inl step) target source back
    exact safe target (Relation.TransGen.tail' old (Or.inr ⟨rfl, rfl⟩))
  · intro noBack x cycle
    rcases path_after_add cycle with oldCycle | ⟨before, after⟩
    · exact acyclic x oldCycle
    · exact noBack (after.trans before)

namespace Controls

inductive ExampleOwner where
  | caller | control | episode | destination
  deriving DecidableEq

/-- The control owns an episode, and the episode owns an internal arena.
The caller is an independent owner that already holds the episode. -/
def edges : ExampleOwner → ExampleOwner → Prop
  | .caller, .episode => True
  | .control, .episode => True
  | .episode, .destination => True
  | _, _ => False

def rank : ExampleOwner → Nat
  | .caller => 3
  | .control => 2
  | .episode => 1
  | .destination => 0

theorem edge_decreases {x y : ExampleOwner} (step : edges x y) : rank y < rank x := by
  cases x <;> cases y <;> simp_all [edges, rank]

theorem path_nonincreasing {x y : ExampleOwner} (path : Relation.ReflTransGen edges x y) :
    rank y ≤ rank x := by
  induction path with
  | refl => exact Nat.le_refl _
  | tail _ step ih => exact Nat.le_trans (Nat.le_of_lt (edge_decreases step)) ih

theorem path_decreases {x y : ExampleOwner} (path : Relation.TransGen edges x y) :
    rank y < rank x := by
  induction path with
  | single step => exact edge_decreases step
  | tail _ step ih => exact Nat.lt_trans (edge_decreases step) ih

theorem edges_acyclic : Acyclic edges := by
  intro x cycle
  exact Nat.lt_irrefl _ (path_decreases cycle)

/-- An episode-owned destination retaining a control closes a real cycle. -/
theorem internal_destination_closes_cycle :
    ¬ Acyclic (add edges .destination .control) := by
  intro safe
  have noBack := (add_acyclic_iff edges_acyclic).mp safe
  apply noBack
  exact .tail (.tail .refl (by simp [edges] : edges .control .episode))
    (by simp [edges] : edges .episode .destination)

/-- An independent caller can retain the same control without that back-edge. -/
theorem independent_caller_stays_acyclic : Acyclic (add edges .caller .control) := by
  apply (add_acyclic_iff edges_acyclic).mpr
  intro back
  have monotone := path_nonincreasing back
  simp [rank] at monotone

end Controls
end Mettapedia.Machines.ResourceOwnership.StrongEdges
