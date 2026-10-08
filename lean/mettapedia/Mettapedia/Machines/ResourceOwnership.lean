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

end Mettapedia.Machines.ResourceOwnership
