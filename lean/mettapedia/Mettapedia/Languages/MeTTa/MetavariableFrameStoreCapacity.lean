import Mettapedia.Languages.MeTTa.MetavariableFrameStore
import Init.Data.List.Nat.Count

/-!
# Usable capacity of the finite-generation shared allocator

A cell contributes capacity exactly when it has no owners and its generation
is below the bound. Retired cells do not count as spare space. The statements
concern the existing allocator operation, independently of any language's
choice of a free handle or any physical allocator implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

def Cell.usable (generationBound : Nat) (cell : Cell) : Bool :=
  decide (cell.owners = 0 ∧ cell.generation < generationBound)

def Allocator.usableCount (allocator : Allocator) : Nat :=
  allocator.cells.toList.countP (Cell.usable allocator.generationBound)

def UsableAt (allocator : Allocator) (handle : Nat) : Prop :=
  ∃ cell, allocator.cells[handle]? = some cell ∧
    cell.owners = 0 ∧ cell.generation < allocator.generationBound

theorem usableAt_bounded {allocator : Allocator} {handle : Nat}
    (usable : UsableAt allocator handle) : handle < allocator.cells.size := by
  obtain ⟨cell, present, _, _⟩ := usable
  exact (Array.getElem?_eq_some_iff.mp present).1

/-- Allocation succeeds at exactly the eligible handles, without requiring
the caller to supply a purported fresh token. -/
theorem allocate_exists_iff (allocator : Allocator) (handle : Nat) :
    (∃ next token, allocate? allocator handle = some (next, token)) ↔ UsableAt allocator handle := by
  cases present : allocator.cells[handle]? with
  | none => simp [allocate?, UsableAt, present]
  | some cell =>
    by_cases eligible : cell.owners = 0 ∧ cell.generation < allocator.generationBound
    · simp [allocate?, UsableAt, present, eligible]
    · simp [allocate?, UsableAt, present, eligible]

/-- Public field-level receipt for the existing allocation. This does not
expose or duplicate the owner's private update operation. -/
theorem allocation_capacity_receipt {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    ∃ cell, allocator.cells[handle]? = some cell ∧ cell.owners = 0 ∧
      cell.generation < allocator.generationBound ∧
      next.cells = allocator.cells.setIfInBounds handle {cell with owners := 1} ∧
      next.generationBound = allocator.generationBound ∧ token = ⟨handle, cell.generation⟩ := by
  cases present : allocator.cells[handle]? with
  | none => simp [allocate?, present] at allocated
  | some cell =>
    simp only [allocate?, present] at allocated
    change (if cell.owners = 0 ∧ cell.generation < allocator.generationBound then
      some ({allocator with cells := allocator.cells.setIfInBounds handle {cell with owners := 1}},
        ⟨handle, cell.generation⟩) else none) = some (next, token) at allocated
    split at allocated
    next eligible =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj allocated)
      exact ⟨cell, rfl, eligible.1, eligible.2, rfl, rfl, rfl⟩
    next => cases allocated

theorem usableCount_pos_iff (allocator : Allocator) :
    0 < allocator.usableCount ↔ ∃ handle, UsableAt allocator handle := by
  rw [Allocator.usableCount, List.countP_pos_iff]
  constructor
  · rintro ⟨cell, member, eligible⟩
    obtain ⟨handle, present⟩ := Array.mem_iff_getElem?.mp (Array.mem_toList_iff.mp member)
    exact ⟨handle, cell, present, by simpa only [Cell.usable, decide_eq_true_eq] using eligible⟩
  · rintro ⟨handle, cell, present, free, below⟩
    exact ⟨cell, Array.mem_toList_iff.mpr (Array.mem_iff_getElem?.mpr ⟨handle, present⟩),
      by simp only [Cell.usable, free, below, and_self, decide_true]⟩

theorem usableCount_pos_iff_allocate (allocator : Allocator) :
    0 < allocator.usableCount ↔ ∃ handle next token, allocate? allocator handle = some (next, token) := by
  rw [usableCount_pos_iff]
  constructor
  · rintro ⟨handle, usable⟩
    obtain ⟨next, token, allocated⟩ := (allocate_exists_iff allocator handle).mpr usable
    exact ⟨handle, next, token, allocated⟩
  · rintro ⟨handle, next, token, allocated⟩
    exact ⟨handle, (allocate_exists_iff allocator handle).mp ⟨next, token, allocated⟩⟩

/-- A successful allocation consumes precisely one usable identity. Neither
the array length nor the generation bound is a substitute for this count. -/
theorem allocate_usableCount {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    next.usableCount + 1 = allocator.usableCount := by
  obtain ⟨cell, present, free, below, cells, bound, _⟩ := allocation_capacity_receipt allocated
  have positive : 0 < allocator.usableCount :=
    (usableCount_pos_iff allocator).mpr ⟨handle, cell, present, free, below⟩
  have listPresent : allocator.cells.toList[handle]? = some cell := by simpa only [Array.getElem?_toList] using present
  obtain ⟨inside, value⟩ := List.getElem?_eq_some_iff.mp listPresent
  have oldEligible : Cell.usable allocator.generationBound cell = true := by simp [Cell.usable, free, below]
  have newIneligible : Cell.usable allocator.generationBound {cell with owners := 1} = false := by simp [Cell.usable]
  have decreased : next.usableCount = allocator.usableCount - 1 := by
    simp only [Allocator.usableCount, cells, bound, Array.toList_setIfInBounds]
    rw [List.countP_set inside, value, oldEligible, newIneligible]
    simp
  omega

theorem allocate_usableCount_sub {allocator next : Allocator} {handle : Nat} {token : Token}
    (allocated : allocate? allocator handle = some (next, token)) :
    next.usableCount = allocator.usableCount - 1 := by
  have exactCount := allocate_usableCount allocated
  omega

theorem Allocator.empty_usableCount (capacity generationBound : Nat) :
    (Allocator.empty capacity generationBound).usableCount = if 0 < generationBound then capacity else 0 := by
  simp [Allocator.empty, Allocator.usableCount, Cell.usable, List.countP_replicate]

theorem initial_positive_generation_has_capacity :
    (Allocator.empty 3 1).usableCount = 3 := by decide

theorem zero_generation_has_no_usable_capacity :
    (Allocator.empty 3 0).usableCount = 0 := by decide

theorem owned_and_retired_cells_are_not_spare :
    (⟨#[⟨0, 1⟩, ⟨4, 0⟩, ⟨3, 0⟩], 4⟩ : Allocator).usableCount = 1 := by decide

end Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
