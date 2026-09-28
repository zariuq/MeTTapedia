import Mettapedia.Machines.ResourceOwnership

/-!
# Conservative growth of finite resource configurations

`Heap` has a finite allocation set in each configuration; its address type is
not required to be finite. Conservative extension keeps every existing cell,
including its payload, references and byte weight, and may allocate new cells.
The old heap's reference closure then makes every path from an old allocated
address stable. With valid old roots, reachability and collection agree in both
directions. Adding roots instead preserves old observations while allowing a
larger live graph.

The reachability relation is the existing `StoreReachability.Reach` through
`ResourceOwnership.Live`. The deployment theory already studies composition of
root/edge relations; here the local premise is preservation of concrete lookup
cells, from which path and collection results are derived. No observation or
reachability equivalence is an assumed field.

This is an allocation/immutable-cell extension law, not a prohibition on mutable
program state. Replacing a cell is a different operation and needs its own
semantic justification. Concurrent mutation, moving addresses, allocator limits
and runtime root discovery remain separate. Finite current configurations do
not imply a uniform bound on future allocation or retained bytes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ResourceOwnership.OpenExtension

universe uValue uOwner

variable {Address : Type} {Value : Type uValue} {Owner : Type uOwner}

/-- A local, full-cell condition: every allocated source cell remains unchanged. -/
def Extends (before after : Heap Address Value) : Prop :=
  ∀ a c, before.lookup a = some c → after.lookup a = some c

@[refl] theorem Extends.refl (h : Heap Address Value) : Extends h h := by
  intro _ _ found
  exact found

@[trans] theorem Extends.trans {first second third : Heap Address Value}
    (left : Extends first second) (right : Extends second third) :
    Extends first third := by
  intro a c found
  exact right a c (left a c found)

theorem Extends.allocated_subset {before after : Heap Address Value}
    (extension : Extends before after) : before.allocated ⊆ after.allocated := by
  intro a present
  obtain ⟨c, found⟩ := (before.allocated_iff a).mp present
  exact (after.allocated_iff a).mpr ⟨c, extension a c found⟩

theorem Extends.lookup_old {before after : Heap Address Value}
    (extension : Extends before after) {a : Address} (present : a ∈ before.allocated) :
    after.lookup a = before.lookup a := by
  obtain ⟨c, found⟩ := (before.allocated_iff a).mp present
  exact (extension a c found).trans found.symm

theorem validRoots_extend {before after : Heap Address Value}
    {roots : Roots Owner Address} (valid : ValidRoots before roots)
    (extension : Extends before after) : ValidRoots after roots := by
  intro pair member
  exact extension.allocated_subset (valid pair member)

/-- Arbitrarily many allocation stages preserve the same local extension law. -/
theorem extends_along {states : Nat → Heap Address Value}
    (step : ∀ n, Extends (states n) (states (n + 1))) {first last : Nat}
    (ordered : first ≤ last) : Extends (states first) (states last) := by
  induction last, ordered using Nat.le_induction with
  | base => exact .refl _
  | succ n _ ih => exact ih.trans (step n)

variable [DecidableEq Address]

/-- Preservation does not need root validity: an existing live derivation
already establishes allocation of its own root. -/
theorem live_preserved {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address) {a : Address}
    (live : Live before roots a) : Live after roots a := by
  induction live with
  | root hr => exact .root ⟨extension.allocated_subset hr.1, hr.2⟩
  | @step a b _ edge ih =>
      obtain ⟨c, found, reference⟩ := edge
      exact live_step after roots ih (extension a c found) reference

/-- Reflection is load-bearing: unchanged old cells cannot introduce a path
from valid old roots into freshly allocated resources. -/
theorem live_reflected {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address)
    (valid : ValidRoots before roots) {a : Address} (live : Live after roots a) :
    Live before roots a := by
  induction live with
  | root hr =>
      obtain ⟨pair, member, same⟩ := Finset.mem_image.mp hr.2
      exact .root ⟨same ▸ valid pair member, hr.2⟩
  | @step a b _ edge ih =>
      obtain ⟨c, found, reference⟩ := edge
      rw [extension.lookup_old (live_allocated before roots ih)] at found
      exact live_step before roots ih found reference

theorem live_iff {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address)
    (valid : ValidRoots before roots) (a : Address) :
    Live after roots a ↔ Live before roots a :=
  ⟨live_reflected extension roots valid, live_preserved extension roots⟩

/-- Every finite path preserves the entire endpoint cell and address. The
proof covers unsuccessful paths as well as successful observations. -/
theorem walk_eq {before after : Heap Address Value}
    (extension : Extends before after) {a : Address} (present : a ∈ before.allocated)
    (path : List Address) : walk after a path = walk before a path := by
  induction path generalizing a with
  | nil => simp only [walk, extension.lookup_old present]
  | cons b rest ih =>
      simp only [walk, extension.lookup_old present]
      obtain ⟨c, found⟩ := (before.allocated_iff a).mp present
      simp only [found, Option.bind_some]
      split
      next reference => exact ih (before.closed a c found b reference)
      next _ => rfl

theorem aliases_iff {before after : Heap Address Value}
    (extension : Extends before after) {a b : Address}
    (leftPresent : a ∈ before.allocated) (rightPresent : b ∈ before.allocated)
    (left right : List Address) :
    Aliases after a left b right ↔ Aliases before a left b right := by
  simp only [Aliases, walk_eq extension leftPresent, walk_eq extension rightPresent]

theorem footprint_eq {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address)
    (valid : ValidRoots before roots) : footprint after roots = footprint before roots := by
  ext a
  simp only [mem_footprint, live_iff extension roots valid]

/-- Collection of the old valid roots removes all fresh unreachable cells,
and retains exactly the same full lookup observations at every address. -/
theorem collect_lookup_eq {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address)
    (valid : ValidRoots before roots) (a : Address) :
    (collect after roots).lookup a = (collect before roots).lookup a := by
  by_cases live : Live before roots a
  · rw [lookup_collect_of_live after roots (live_preserved extension roots live),
      lookup_collect_of_live before roots live]
    exact extension.lookup_old (live_allocated before roots live)
  · rw [lookup_collect_of_not_live before roots live,
      lookup_collect_of_not_live after roots
        (fun liveAfter => live (live_reflected extension roots valid liveAfter))]

theorem collect_allocated_eq {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address)
    (valid : ValidRoots before roots) :
    (collect after roots).allocated = (collect before roots).allocated :=
  footprint_eq extension roots valid

theorem retainedBytes_eq {before after : Heap Address Value}
    (extension : Extends before after) (roots : Roots Owner Address)
    (valid : ValidRoots before roots) : retainedBytes after roots = retainedBytes before roots := by
  unfold retainedBytes
  rw [footprint_eq extension roots valid]
  apply Finset.sum_congr rfl
  intro a member
  simp only [cellBytes, extension.lookup_old
    (live_allocated before roots ((mem_footprint before roots a).mp member))]

/-- New owners or roots can protect more cells without invalidating old live
paths. This does not assert that the enlarged live set equals the old one. -/
theorem live_with_more_roots {before after : Heap Address Value}
    (extension : Extends before after) {roots more : Roots Owner Address}
    (subset : roots ⊆ more) {a : Address} (live : Live before roots a) :
    Live after more a := live_mono after subset (live_preserved extension roots live)

theorem collected_walk_with_more_roots {before after : Heap Address Value}
    (extension : Extends before after) {roots more : Roots Owner Address}
    (subset : roots ⊆ more) {a : Address} (live : Live before roots a)
    (path : List Address) : walk (collect after more) a path = walk before a path := by
  rw [walk_collect after more (live_with_more_roots extension subset live)]
  exact walk_eq extension (live_allocated before roots live) path

/-! ## A concrete allocation operation -/

/-- Insert or replace one reference-closed cell. Fresh insertion is proved
conservative below; replacement deliberately has no such blanket guarantee. -/
def put (h : Heap Address Value) (address : Address) (cell : Cell Address Value)
    (references : ∀ b ∈ cell.references, b = address ∨ b ∈ h.allocated) :
    Heap Address Value where
  lookup a := if a = address then some cell else h.lookup a
  allocated := insert address h.allocated
  allocated_iff a := by
    by_cases same : a = address
    · simp [same]
    · simp only [Finset.mem_insert, same, false_or]
      exact h.allocated_iff a
  closed := by
    intro a c found b reference
    by_cases same : a = address
    · simp only [same, if_pos, Option.some.injEq] at found
      subst c
      exact Finset.mem_insert.mpr (references b reference)
    · simp only [if_neg same] at found
      exact Finset.mem_insert_of_mem (h.closed a c found b reference)

theorem extends_put_of_fresh (h : Heap Address Value) (address : Address)
    (cell : Cell Address Value)
    (references : ∀ b ∈ cell.references, b = address ∨ b ∈ h.allocated)
    (fresh : address ∉ h.allocated) : Extends h (put h address cell references) := by
  intro a c found
  have different : a ≠ address := by
    intro same
    exact fresh (same ▸ (h.allocated_iff a).mpr ⟨c, found⟩)
  simp only [put, if_neg different, found]

/-- Any current heap over natural addresses can allocate another cell. No
fixed finite universe or maximum future allocation count is involved. -/
theorem can_grow (h : Heap Nat Value) (value : Value) :
    ∃ after : Heap Nat Value, Extends h after ∧
      after.allocated.card = h.allocated.card + 1 := by
  obtain ⟨fresh, covered⟩ := Finset.exists_nat_subset_range h.allocated
  have absent : fresh ∉ h.allocated := by
    intro present
    have := Finset.mem_range.mp (covered present)
    omega
  let cell : Cell Nat Value := ⟨value, {fresh}, 1⟩
  have references : ∀ b ∈ cell.references, b = fresh ∨ b ∈ h.allocated := by
    intro b member
    exact Or.inl (Finset.mem_singleton.mp member)
  refine ⟨put h fresh cell references, extends_put_of_fresh _ _ _ _ absent, ?_⟩
  exact Finset.card_insert_of_notMem absent

/-- Local finiteness plus a single owner-root gives no uniform memory bound.
This reuses the existing arbitrarily long reachable-chain construction. -/
theorem no_uniform_one_root_bound :
    ¬ ∃ bound, ∀ (h : Heap Nat Nat) (roots : Roots Unit Nat),
      roots.card = 1 → retainedBytes h roots ≤ bound := by
  rintro ⟨bound, bounded⟩
  obtain ⟨h, roots, one, larger⟩ := Examples.one_root_unbounded bound
  exact Nat.not_lt_of_ge (bounded h roots one) larger

/-! ## Fresh growth, new roots, and rejected replacements -/

namespace Controls

def before : Heap Nat Nat := Examples.chainHeap 1
def roots : Roots Nat Nat := {(0, 0)}

/-- A fresh resource points both to the old graph and to itself. -/
def freshCell : Cell Nat Nat := ⟨42, {0, 2}, 8⟩

def after : Heap Nat Nat := put before 2 freshCell (by
  intro b member
  simp only [freshCell, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact Or.inr (by decide)
  · exact Or.inl rfl)

theorem grows : Extends before after :=
  extends_put_of_fresh before 2 freshCell _ (by decide)

theorem roots_valid : ValidRoots before roots := by
  intro pair member
  have : pair = (0, 0) := Finset.mem_singleton.mp member
  subst pair
  decide

theorem fresh_allocation : after.allocated.card = before.allocated.card + 1 := by decide

theorem old_full_path : walk after 0 [1] = walk before 0 [1] :=
  walk_eq grows (by decide) [1]

theorem old_collection :
    (collect after roots).lookup = (collect before roots).lookup := by
  funext a
  exact collect_lookup_eq grows roots roots_valid a

def moreRoots : Roots Nat Nat := {(0, 0), (1, 2)}

theorem new_root_protects_fresh_cycle : Live after moreRoots 2 :=
  live_of_root after moreRoots (owner := 1) (by decide) (by decide)

theorem new_root_reaches_old_graph : Live after ({(1, 2)} : Roots Nat Nat) 1 := by
  have atTwo : Live after ({(1, 2)} : Roots Nat Nat) 2 :=
    live_of_root after _ (owner := 1) (by decide) (by decide)
  have atZero := live_step after _ atTwo (show after.lookup 2 = some freshCell by decide)
    (show 0 ∈ freshCell.references by decide)
  exact live_step after _ atZero (show after.lookup 0 = some (Examples.chainCell 1 0) by decide)
    (by decide)

theorem fresh_cell_needs_new_root :
    (collect after roots).lookup 2 = none ∧
      (collect after moreRoots).lookup 2 = some freshCell := by
  constructor
  · rw [collect_lookup_eq grows roots roots_valid]
    apply lookup_collect_of_not_live
    intro live
    have := live_allocated before roots live
    simp [before, Examples.chainHeap] at this
  · rw [lookup_collect_of_live after moreRoots new_root_protects_fresh_cycle]
    decide

/-- Without root validity an old dangling root becomes live after allocation. -/
theorem invalid_root_breaks_reflection :
    ¬ Live before ({(1, 2)} : Roots Nat Nat) 2 ∧
      Live after ({(1, 2)} : Roots Nat Nat) 2 := by
  constructor
  · intro live
    have := live_allocated before _ live
    simp [before, Examples.chainHeap] at this
  · exact live_of_root after _ (owner := 1) (by decide) (by decide)

def changedPayload : Heap Nat Nat :=
  put before 0 ⟨99, {1}, 1⟩ (by
    intro b member
    have : b = 1 := Finset.mem_singleton.mp member
    subst b
    exact Or.inr (by decide))

theorem payload_replacement_is_not_extension : ¬ Extends before changedPayload := by
  intro extension
  have same := extension.lookup_old (show 0 ∈ before.allocated by decide)
  have different : changedPayload.lookup 0 ≠ before.lookup 0 := by decide
  exact different same

theorem payload_replacement_changes_full_cell :
    walk changedPayload 0 [] ≠ walk before 0 [] := by decide

def deletedEdge : Heap Nat Nat :=
  put before 0 ⟨0, ∅, 1⟩ (by simp)

theorem edge_deletion_changes_path :
    deletedEdge.allocated = before.allocated ∧
      walk deletedEdge 0 [1] = none ∧ walk before 0 [1] ≠ none := by decide

theorem edge_deletion_is_not_extension : ¬ Extends before deletedEdge := by
  intro extension
  have same := walk_eq extension (show 0 ∈ before.allocated by decide) [1]
  have different : walk deletedEdge 0 [1] ≠ walk before 0 [1] := by decide
  exact different same

end Controls

end Mettapedia.Machines.ResourceOwnership.OpenExtension
