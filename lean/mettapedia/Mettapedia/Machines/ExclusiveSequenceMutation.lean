import Mettapedia.Machines.ResourceOwnership

/-!
# Appending to an exclusively owned logical sequence buffer

Two actual finite-heap operations are compared: replace an allocated cell at
its current address, or allocate the updated cell at a fresh address and
redirect the selected root. The selected result is observed as a logical
sequence. Every other root retains its complete cell/path observations and
successful-path aliases, including identity, payload, outgoing references and
declared byte weight.

Exclusivity excludes every transitive route from another root occurrence to
the selected buffer. Counting its direct roots is insufficient. Another root
of the same owner is excluded too. `Roots` is a finite set of pairs, so runtime
handles with identical pairs must either have distinct occurrence labels or
be separately proved affine; a set cannot count indistinguishable aliases.

Appended elements contribute explicit strong references, all already allocated.
The surrounding heap can have sharing and cycles. The selected buffer's address
is intentionally outside its logical sequence observation: allocation changes
that address. Deep observations through elements that refer back to the buffer
are not identified by this theorem. Physical capacity, allocator behavior,
concurrent mutation and a concrete queue implementation are not modeled.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ExclusiveSequenceMutation

open ResourceOwnership

variable {Address Element Owner : Type}
variable [DecidableEq Address]

/-- The complete appended reference set does not require equality on elements. -/
def elementReferences (references : Element → Finset Address) :
    List Element → Finset Address
  | [] => ∅
  | value :: rest => references value ∪ elementReferences references rest

def appendCell (cell : Cell Address (List Element)) (suffix : List Element)
    (references : Element → Finset Address) (bytes : Nat) : Cell Address (List Element) :=
  ⟨cell.value ++ suffix, cell.references ∪ elementReferences references suffix, bytes⟩

/-- Replace a cell at an existing address. All other lookup entries survive. -/
def replace (heap : Heap Address (List Element)) (target : Address)
    (cell : Cell Address (List Element)) (present : target ∈ heap.allocated)
    (safe : cell.references ⊆ heap.allocated) : Heap Address (List Element) where
  lookup address := if address = target then some cell else heap.lookup address
  allocated := heap.allocated
  allocated_iff address := by
    by_cases same : address = target
    · subst address
      simp [present]
    · simpa [same] using heap.allocated_iff address
  closed address foundCell found next reference := by
    by_cases same : address = target
    · simp [same] at found
      subst foundCell
      exact safe reference
    · simp only [if_neg same] at found
      exact heap.closed address foundCell found next reference

/-- Fresh allocation preserves every old cell. Its edges point to existing
resources; allocation itself cannot install a dangling outgoing edge. -/
def allocate (heap : Heap Address (List Element)) (fresh : Address)
    (cell : Cell Address (List Element)) (_unused : fresh ∉ heap.allocated)
    (safe : cell.references ⊆ heap.allocated) : Heap Address (List Element) where
  lookup address := if address = fresh then some cell else heap.lookup address
  allocated := insert fresh heap.allocated
  allocated_iff address := by
    by_cases same : address = fresh
    · subst address
      simp
    · simpa [same] using heap.allocated_iff address
  closed address foundCell found next reference := by
    by_cases same : address = fresh
    · simp [same] at found
      subst foundCell
      exact Finset.mem_insert_of_mem (safe reference)
    · simp only [if_neg same] at found
      exact Finset.mem_insert_of_mem (heap.closed address foundCell found next reference)

@[simp] theorem lookup_replace_same (heap : Heap Address (List Element))
    (target : Address) (cell : Cell Address (List Element)) (present safe) :
    (replace heap target cell present safe).lookup target = some cell := by
  simp [replace]

theorem lookup_replace_other (heap : Heap Address (List Element))
    (target address : Address) (cell : Cell Address (List Element)) (present safe)
    (other : address ≠ target) :
    (replace heap target cell present safe).lookup address = heap.lookup address := by
  simp [replace, other]

@[simp] theorem lookup_allocate_fresh (heap : Heap Address (List Element))
    (fresh : Address) (cell : Cell Address (List Element)) (unused safe) :
    (allocate heap fresh cell unused safe).lookup fresh = some cell := by
  simp [allocate]

theorem lookup_allocate_old (heap : Heap Address (List Element))
    (fresh address : Address) (cell : Cell Address (List Element)) (unused safe)
    (old : address ∈ heap.allocated) :
    (allocate heap fresh cell unused safe).lookup address = heap.lookup address := by
  have different : address ≠ fresh := by
    intro same
    exact unused (same ▸ old)
  simp [allocate, different]

/-- Full path observations are unchanged away from the replaced cell's
transitive footprint. This includes paths that fail partway through. -/
theorem walk_replace_of_not_live (heap : Heap Address (List Element))
    (roots : Roots Owner Address) (target : Address)
    (cell : Cell Address (List Element)) (present safe)
    (exclusive : ¬ Live heap roots target) {address : Address}
    (live : Live heap roots address) (path : List Address) :
    walk (replace heap target cell present safe) address path = walk heap address path := by
  induction path generalizing address with
  | nil =>
      have different : address ≠ target := fun same => exclusive (same ▸ live)
      simp only [walk, lookup_replace_other heap target address cell present safe different]
  | cons next rest ih =>
      have different : address ≠ target := fun same => exclusive (same ▸ live)
      simp only [walk, lookup_replace_other heap target address cell present safe different]
      obtain ⟨oldCell, found⟩ :=
        (heap.allocated_iff address).mp (live_allocated heap roots live)
      simp only [found, Option.bind_some]
      split
      next reference => exact ih (live_step heap roots live found reference)
      next _ => rfl

/-- Changing outgoing edges of an unreachable cell cannot create a first
route to that cell, or to any other newly reachable resource, from these roots. -/
theorem live_replace_reflect (heap : Heap Address (List Element))
    (roots : Roots Owner Address) (target : Address)
    (cell : Cell Address (List Element)) (present safe)
    (unreachable : ¬ Live heap roots target) {address : Address}
    (live : Live (replace heap target cell present safe) roots address) :
    Live heap roots address := by
  induction live with
  | root rooted => exact .root rooted
  | @step previous address _ edge ih =>
      obtain ⟨oldCell, found, reference⟩ := edge
      have different : previous ≠ target := fun same => unreachable (same ▸ ih)
      rw [lookup_replace_other heap target previous cell present safe different] at found
      exact live_step heap roots ih found reference

/-- A fresh allocation cannot change a path starting at an old allocated
cell: reference closure prevents that path from reaching the fresh address. -/
theorem walk_allocate_old (heap : Heap Address (List Element))
    (fresh : Address) (cell : Cell Address (List Element)) (unused safe)
    {address : Address} (old : address ∈ heap.allocated) (path : List Address) :
    walk (allocate heap fresh cell unused safe) address path = walk heap address path := by
  induction path generalizing address with
  | nil => simp only [walk, lookup_allocate_old heap fresh address cell unused safe old]
  | cons next rest ih =>
      simp only [walk, lookup_allocate_old heap fresh address cell unused safe old]
      obtain ⟨oldCell, found⟩ := (heap.allocated_iff address).mp old
      simp only [found, Option.bind_some]
      split
      next reference => exact ih (heap.closed address oldCell found next reference)
      next _ => rfl

/-- No other root occurrence, including one of the same owner, can reach the
buffer. This is a condition on paths in the actual heap, not direct counts. -/
def Exclusive (heap : Heap Address (List Element)) (roots : Roots Owner Address)
    (selected : Owner × Address) : Prop :=
  ∀ root ∈ roots, root ≠ selected → ¬ Live heap {root} selected.2

theorem append_references_safe (heap : Heap Address (List Element))
    {target : Address} {old : Cell Address (List Element)}
    (found : heap.lookup target = some old) (suffix : List Element)
    (references : Element → Finset Address) (bytes : Nat)
    (newSafe : elementReferences references suffix ⊆ heap.allocated) :
    (appendCell old suffix references bytes).references ⊆ heap.allocated := by
  intro address member
  rcases Finset.mem_union.mp member with existing | added
  · exact heap.closed target old found address existing
  · exact newSafe added

def appendInPlace (heap : Heap Address (List Element)) (target : Address)
    (old : Cell Address (List Element)) (found : heap.lookup target = some old)
    (suffix : List Element) (references : Element → Finset Address) (bytes : Nat)
    (newSafe : elementReferences references suffix ⊆ heap.allocated) :
    Heap Address (List Element) :=
  replace heap target (appendCell old suffix references bytes)
    ((heap.allocated_iff target).mpr ⟨old, found⟩)
    (append_references_safe heap found suffix references bytes newSafe)

def appendFresh (heap : Heap Address (List Element)) (target fresh : Address)
    (old : Cell Address (List Element)) (found : heap.lookup target = some old)
    (unused : fresh ∉ heap.allocated) (suffix : List Element)
    (references : Element → Finset Address) (bytes : Nat)
    (newSafe : elementReferences references suffix ⊆ heap.allocated) :
    Heap Address (List Element) :=
  allocate heap fresh (appendCell old suffix references bytes) unused
    (append_references_safe heap found suffix references bytes newSafe)

/-- The condition can be reused for another append, provided no new roots
are introduced. Newly appended outgoing references cannot make another owner
acquire a route into the buffer being updated. -/
theorem exclusive_after_append (heap : Heap Address (List Element))
    (roots : Roots Owner Address) (selected : Owner × Address)
    (exclusive : Exclusive heap roots selected)
    (old : Cell Address (List Element)) (found) (suffix : List Element)
    (references : Element → Finset Address) (bytes : Nat) (newSafe) :
    Exclusive (appendInPlace heap selected.2 old found suffix references bytes newSafe)
      roots selected := by
  intro root member other live
  apply exclusive root member other
  exact live_replace_reflect heap {root} selected.2 _ _ _
    (exclusive root member other) live

/-- Logical buffer observation omits storage address and physical capacity. -/
def sequenceAt (heap : Heap Address (List Element)) (address : Address) :
    Option (List Element) := (heap.lookup address).map Cell.value

theorem appended_sequence_in_place (heap : Heap Address (List Element)) (target : Address)
    (old : Cell Address (List Element)) (found) (suffix : List Element)
    (references : Element → Finset Address) (bytes : Nat) (newSafe) :
    sequenceAt (appendInPlace heap target old found suffix references bytes newSafe) target =
      some (old.value ++ suffix) := by
  simp [sequenceAt, appendInPlace, appendCell]

theorem appended_sequence_fresh (heap : Heap Address (List Element)) (target fresh : Address)
    (old : Cell Address (List Element)) (found unused) (suffix : List Element)
    (references : Element → Finset Address) (bytes : Nat) (newSafe) :
    sequenceAt (appendFresh heap target fresh old found unused suffix references bytes newSafe)
      fresh = some (old.value ++ suffix) := by
  simp [sequenceAt, appendFresh, appendCell]

/-- Every nonselected root observes exactly the same complete path result
after in-place append and fresh allocation. The result address is preserved. -/
theorem other_root_walks_agree (heap : Heap Address (List Element))
    (roots : Roots Owner Address) (selected : Owner × Address)
    (rooted : ValidRoots heap roots) (exclusive : Exclusive heap roots selected)
    (fresh : Address) (old : Cell Address (List Element)) (found unused)
    (suffix : List Element) (references : Element → Finset Address) (bytes : Nat) (newSafe)
    (root : Owner × Address) (member : root ∈ roots) (other : root ≠ selected)
    (path : List Address) :
    walk (appendInPlace heap selected.2 old found suffix references bytes newSafe) root.2 path =
      walk (appendFresh heap selected.2 fresh old found unused suffix references bytes newSafe)
        root.2 path := by
  have live : Live heap {root} root.2 :=
    live_of_root heap {root} (Finset.mem_singleton_self _) (rooted root member)
  rw [appendInPlace, walk_replace_of_not_live heap {root} selected.2 _ _ _
    (exclusive root member other) live]
  exact (walk_allocate_old heap fresh _ _ _ (rooted root member) path).symm

/-- Alias preservation is bidirectional; no pair of successful paths is
silently merged or separated for the other roots. -/
theorem other_root_aliases_agree (heap : Heap Address (List Element))
    (roots : Roots Owner Address) (selected : Owner × Address)
    (rooted : ValidRoots heap roots) (exclusive : Exclusive heap roots selected)
    (fresh : Address) (old : Cell Address (List Element)) (found unused)
    (suffix : List Element) (references : Element → Finset Address) (bytes : Nat) (newSafe)
    (left right : Owner × Address) (leftMember : left ∈ roots) (rightMember : right ∈ roots)
    (leftOther : left ≠ selected) (rightOther : right ≠ selected)
    (leftPath rightPath : List Address) :
    Aliases (appendInPlace heap selected.2 old found suffix references bytes newSafe)
      left.2 leftPath right.2 rightPath ↔
    Aliases (appendFresh heap selected.2 fresh old found unused suffix references bytes newSafe)
      left.2 leftPath right.2 rightPath := by
  unfold Aliases
  rw [other_root_walks_agree heap roots selected rooted exclusive fresh old found unused
    suffix references bytes newSafe left leftMember leftOther leftPath]
  rw [other_root_walks_agree heap roots selected rooted exclusive fresh old found unused
    suffix references bytes newSafe right rightMember rightOther rightPath]

variable [DecidableEq Owner]

def redirect (roots : Roots Owner Address) (selected : Owner × Address)
    (fresh : Address) : Roots Owner Address :=
  insert (selected.1, fresh) (roots.erase selected)

theorem redirected_root_present (roots : Roots Owner Address)
    (selected : Owner × Address) (fresh : Address) :
    (selected.1, fresh) ∈ redirect roots selected fresh := by simp [redirect]

theorem other_root_retained (roots : Roots Owner Address) (selected root : Owner × Address)
    (fresh : Address) (member : root ∈ roots) (other : root ≠ selected) :
    root ∈ redirect roots selected fresh := by simp [redirect, member, other]

/-- The complete comparison: selected sequence content, the actual redirected
root, and every untouched root's full heap-path observations. -/
theorem append_refines_fresh (heap : Heap Address (List Element))
    (roots : Roots Owner Address) (selected : Owner × Address)
    (selectedMember : selected ∈ roots) (rooted : ValidRoots heap roots)
    (exclusive : Exclusive heap roots selected)
    (fresh : Address) (old : Cell Address (List Element)) (found unused)
    (suffix : List Element) (references : Element → Finset Address) (bytes : Nat) (newSafe) :
    let inPlace := appendInPlace heap selected.2 old found suffix references bytes newSafe
    let copied := appendFresh heap selected.2 fresh old found unused suffix references bytes newSafe
    let copiedRoots := redirect roots selected fresh
    Live inPlace roots selected.2 ∧
      Live copied copiedRoots fresh ∧
      sequenceAt inPlace selected.2 = sequenceAt copied fresh ∧
      ∀ root ∈ roots, root ≠ selected →
        root ∈ copiedRoots ∧ ∀ path, walk inPlace root.2 path = walk copied root.2 path := by
  dsimp only
  refine ⟨live_of_root _ roots selectedMember (rooted selected selectedMember), ?_, ?_, ?_⟩
  · exact live_of_root _ _ (redirected_root_present roots selected fresh)
      (Finset.mem_insert_self _ _)
  · rw [appended_sequence_in_place, appended_sequence_fresh]
  · intro root member other
    exact ⟨other_root_retained roots selected root fresh member other,
      other_root_walks_agree heap roots selected rooted exclusive fresh old found unused
        suffix references bytes newSafe root member other⟩

namespace Controls

/-- In the unshared case, the other owner's two cells form a cycle. In the
shared case that route instead reaches the buffer through two edges. -/
def demoLookup (shared : Bool) : Nat → Option (Cell Nat (List Nat))
  | 0 => some ⟨[4, 5], ∅, 2⟩
  | 1 => some ⟨[10], {2}, 1⟩
  | 2 => some ⟨[20], if shared then {0} else {1}, 1⟩
  | _ + 3 => none

def demo (shared : Bool) : Heap Nat (List Nat) where
  lookup := demoLookup shared
  allocated := {0, 1, 2}
  allocated_iff address := by
    rcases address with _ | (_ | (_ | address)) <;> simp [demoLookup]
  closed address cell found next reference := by
    rcases address with _ | (_ | (_ | address)) <;>
      simp only [demoLookup] at found
    · cases found
      simp at reference
    · cases found
      simp_all
    · cases found
      cases shared <;> simp_all
    · cases found

def roots : Roots Nat Nat := {(0, 0), (1, 1)}

theorem roots_allocated (shared : Bool) : ValidRoots (demo shared) roots := by
  intro root member
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl <;> simp [demo]

theorem unshared_live_is_other {address : Nat}
    (live : Live (demo false) ({(1, 1)} : Roots Nat Nat) address) :
    address = 1 ∨ address = 2 := by
  induction live with
  | @root address rooted =>
      have first : address = 1 := by
        simpa [Heap.toStore, rootAddresses] using rooted.2
      exact .inl first
  | @step previous address _ edge ih =>
      obtain ⟨cell, found, reference⟩ := edge
      rcases ih with rfl | rfl
      · simp only [demo, demoLookup, Option.some.injEq] at found
        subst cell
        exact .inr (by simpa using reference)
      · simp only [demo, demoLookup, Bool.false_eq_true, if_false,
          Option.some.injEq] at found
        subst cell
        exact .inl (by simpa using reference)

theorem unshared_exclusive : Exclusive (demo false) roots (0, 0) := by
  intro root member other live
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · exact other rfl
  · have impossible := unshared_live_is_other live
    omega

/-- The new element itself refers to an existing shared resource. -/
def newReferences (value : Nat) : Finset Nat := if value = 3 then {2} else ∅

theorem new_references_allocated (shared : Bool) :
    elementReferences newReferences [3] ⊆ (demo shared).allocated := by
  simp [elementReferences, newReferences, demo]

def grown (shared : Bool) : Heap Nat (List Nat) :=
  appendInPlace (demo shared) 0 ⟨[4, 5], ∅, 2⟩ rfl [3] newReferences 3
    (new_references_allocated shared)

def copied (shared : Bool) : Heap Nat (List Nat) :=
  appendFresh (demo shared) 0 3 ⟨[4, 5], ∅, 2⟩ rfl (by simp [demo]) [3] newReferences 3
    (new_references_allocated shared)

theorem unshared_append_observation :
    sequenceAt (grown false) 0 = some [4, 5, 3] ∧
      sequenceAt (copied false) 3 = some [4, 5, 3] := by decide

/-- Arbitrarily long paths around the other owner's cycle are preserved. -/
theorem unshared_cycle_paths (path : List Nat) :
    walk (grown false) 1 path = walk (copied false) 1 path := by
  exact other_root_walks_agree (demo false) roots (0, 0) (roots_allocated false)
    unshared_exclusive 3 ⟨[4, 5], ∅, 2⟩ rfl (by decide) [3] newReferences 3
    (new_references_allocated false) (1, 1) (by decide) (by decide) path

theorem unshared_cycle_aliases (left right : List Nat) :
    Aliases (grown false) 1 left 1 right ↔ Aliases (copied false) 1 left 1 right := by
  exact other_root_aliases_agree (demo false) roots (0, 0) (roots_allocated false)
    unshared_exclusive 3 ⟨[4, 5], ∅, 2⟩ rfl (by decide) [3] newReferences 3
    (new_references_allocated false) (1, 1) (1, 1)
    (by decide) (by decide) (by decide) (by decide) left right

/-- There is only one direct root at the buffer even in the shared case. -/
theorem unique_direct_root :
    ∀ root ∈ roots, root.2 = 0 → root = (0, 0) := by
  intro root member atBuffer
  simp only [roots, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl
  · rfl
  · cases atBuffer

theorem shared_indirect_root :
    Live (demo true) ({(1, 1)} : Roots Nat Nat) 0 := by
  have start : Live (demo true) ({(1, 1)} : Roots Nat Nat) 1 :=
    live_of_root _ _ (Finset.mem_singleton_self _) (by decide)
  have middle : Live (demo true) ({(1, 1)} : Roots Nat Nat) 2 :=
    live_step _ _ start rfl (by decide)
  exact live_step _ _ middle rfl (by decide)

theorem shared_indirect_rejected : ¬ Exclusive (demo true) roots (0, 0) := by
  intro exclusive
  exact exclusive (1, 1) (by decide) (by decide) shared_indirect_root

/-- A transitive alias observes the changed sibling value after unsafe
mutation; fresh allocation leaves that sibling's value intact. -/
theorem shared_append_changes_sibling :
    (walk (grown true) 1 [2, 0]).map (fun result => result.2.value) ≠
      (walk (copied true) 1 [2, 0]).map (fun result => result.2.value) := by decide

theorem same_owner_alias_rejected :
    ¬ Exclusive (demo true) ({(0, 0), (0, 1)} : Roots Nat Nat) (0, 0) := by
  intro exclusive
  have start : Live (demo true) ({(0, 1)} : Roots Nat Nat) 1 :=
    live_of_root _ _ (Finset.mem_singleton_self _) (by decide)
  have middle : Live (demo true) ({(0, 1)} : Roots Nat Nat) 2 :=
    live_step _ _ start rfl (by decide)
  exact exclusive (0, 1) (by decide) (by decide)
    (live_step _ _ middle rfl (by decide))

/-- Logical equality intentionally does not identify the two storage addresses. -/
theorem selected_storage_identity_differs :
    (walk (grown false) 0 []).map Prod.fst = some 0 ∧
      (walk (copied false) 3 []).map Prod.fst = some 3 := by decide

end Controls

#print axioms lookup_replace_same
#print axioms lookup_replace_other
#print axioms lookup_allocate_fresh
#print axioms lookup_allocate_old
#print axioms walk_replace_of_not_live
#print axioms live_replace_reflect
#print axioms walk_allocate_old
#print axioms append_references_safe
#print axioms exclusive_after_append
#print axioms appended_sequence_in_place
#print axioms appended_sequence_fresh
#print axioms other_root_walks_agree
#print axioms other_root_aliases_agree
#print axioms redirected_root_present
#print axioms other_root_retained
#print axioms append_refines_fresh
#print axioms Controls.roots_allocated
#print axioms Controls.unshared_live_is_other
#print axioms Controls.unshared_exclusive
#print axioms Controls.new_references_allocated
#print axioms Controls.unshared_append_observation
#print axioms Controls.unshared_cycle_paths
#print axioms Controls.unshared_cycle_aliases
#print axioms Controls.unique_direct_root
#print axioms Controls.shared_indirect_root
#print axioms Controls.shared_indirect_rejected
#print axioms Controls.shared_append_changes_sibling
#print axioms Controls.same_owner_alias_rejected
#print axioms Controls.selected_storage_identity_differs

end Mettapedia.Machines.ExclusiveSequenceMutation
