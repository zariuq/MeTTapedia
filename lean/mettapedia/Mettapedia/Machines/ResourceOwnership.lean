import Mettapedia.GSLT.Dynamics.StoreReachability
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

end Relocation

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

end Examples

end Mettapedia.Machines.ResourceOwnership
