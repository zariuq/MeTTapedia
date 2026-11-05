import Mettapedia.Languages.MeTTa.MetavariableFrameStoreCapacity
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ConstantQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PresenceGuardSource

/-!
# Exact usable capacity for scalar answer copies

The actual finite-range search succeeds exactly when a usable identity
exists. A scalar with no associated syntax has no names to avoid, so its
copy uses the same search. This does not assert availability for arbitrary
variable-bearing packets or replace generation validity with array capacity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS.Collection (allocateAnswer? allocateAnswer_origin allocateCopy?)

theorem allocateAnswer_exists_iff (allocator : Allocator) :
    (∃ next token, allocateAnswer? allocator = some (next, token)) ↔ 0 < allocator.usableCount := by
  constructor
  · rintro ⟨next, token, allocated⟩
    obtain ⟨handle, _, actual⟩ := allocateAnswer_origin allocated
    exact (usableCount_pos_iff_allocate allocator).mpr ⟨handle, next, token, actual⟩
  · intro positive
    obtain ⟨handle, next, token, allocated⟩ := (usableCount_pos_iff_allocate allocator).mp positive
    have bounded := usableAt_bounded ((allocate_exists_iff allocator handle).mp ⟨next, token, allocated⟩)
    cases searched : allocateAnswer? allocator with
    | none =>
      have missing := List.findSome?_eq_none_iff.mp searched handle (List.mem_range.mpr bounded)
      rw [allocated] at missing
      cases missing
    | some result => exact ⟨result.1, result.2, rfl⟩

theorem allocateAnswer_usableCount {allocator next : Allocator} {token : Token}
    (allocated : allocateAnswer? allocator = some (next, token)) :
    next.usableCount + 1 = allocator.usableCount := by
  obtain ⟨handle, _, actual⟩ := allocateAnswer_origin allocated
  exact allocate_usableCount actual

theorem allocateCopy_exists_iff {payload : Atom} (scalar : ConstantQuerySource.Scalar payload)
    (allocator : Allocator) (protectedNames : Finset String) :
    (∃ next token, allocateCopy? allocator protectedNames payload [] = some (next, token)) ↔
      0 < allocator.usableCount := by
  rw [scalar.allocateCopy]
  exact allocateAnswer_exists_iff allocator

theorem allocateCopy_usableCount {payload : Atom} (scalar : ConstantQuerySource.Scalar payload)
    {allocator next : Allocator} {protectedNames : Finset String} {token : Token}
    (copied : allocateCopy? allocator protectedNames payload [] = some (next, token)) :
    next.usableCount + 1 = allocator.usableCount := by
  rw [scalar.allocateCopy] at copied
  exact allocateAnswer_usableCount copied

theorem copyAllocator_true_exists_iff (allocator : Allocator) :
    (∃ next, PresenceGuardSource.copyAllocator allocator true = some next) ↔ 0 < allocator.usableCount := by
  constructor
  · rintro ⟨next, copied⟩
    change (allocateAnswer? allocator).map Prod.fst = some next at copied
    obtain ⟨result, allocated, _⟩ := Option.map_eq_some_iff.mp copied
    exact (allocateAnswer_exists_iff allocator).mp ⟨result.1, result.2, allocated⟩
  · intro positive
    obtain ⟨next, token, allocated⟩ := (allocateAnswer_exists_iff allocator).mpr positive
    exact ⟨next, by simp [PresenceGuardSource.copyAllocator, allocated]⟩

theorem copyAllocator_true_usableCount {allocator next : Allocator}
    (copied : PresenceGuardSource.copyAllocator allocator true = some next) :
    next.usableCount + 1 = allocator.usableCount := by
  change (allocateAnswer? allocator).map Prod.fst = some next at copied
  obtain ⟨⟨middle, token⟩, allocated, same⟩ := Option.map_eq_some_iff.mp copied
  change middle = next at same
  subst next
  exact allocateAnswer_usableCount allocated

theorem false_guard_uses_no_copy (allocator : Allocator) :
    PresenceGuardSource.copyAllocator allocator false = some allocator := rfl

theorem retired_prefix_does_not_hide_a_usable_cell :
    ∃ next token, allocateAnswer? (⟨#[⟨2, 0⟩, ⟨0, 0⟩], 2⟩ : Allocator) = some (next, token) :=
  (allocateAnswer_exists_iff _).mpr (by decide)

theorem retired_capacity_is_not_allocation_capacity :
    allocateAnswer? (⟨#[⟨2, 0⟩, ⟨2, 0⟩], 2⟩ : Allocator) = none := by decide

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScalarCopyCapacity
