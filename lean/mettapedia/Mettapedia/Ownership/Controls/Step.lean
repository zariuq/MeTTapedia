import Mettapedia.Ownership.Step

/-!
# Controls: steps

Plans admitted and refused by the step, run from the initial state.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

namespace Controls

def rootPlan : List Action := [.root 1 16 .exclusive .local 0,
  .borrow 2 1 ⟨1, 0, 8⟩ .exclusive, .borrow 3 1 ⟨1, 8, 8⟩ .exclusive]

def run : State → List Action → Option State
  | s, [] => some s
  | s, a :: rest => (apply s a).bind fun after => run after rest

theorem separate_fields_admitted : (run initial (rootPlan ++
    [.access 2 ⟨1, 0, 8⟩ true, .access 3 ⟨1, 8, 8⟩ true])).isSome = true := by decide

theorem overlapping_fields_refused : run initial (rootPlan ++
    [.borrow 4 1 ⟨1, 4, 8⟩ .exclusive]) = none := by decide

theorem use_after_scope_refused : run initial
    [.root 1 4 .exclusive .local 0, .endLoan 1, .access 1 ⟨1, 0, 4⟩ false] = none := by decide

theorem borrow_does_not_acquire_release : run initial
    [.root 1 4 .exclusive .heap 9, .borrow 2 1 ⟨1, 0, 4⟩ .exclusive,
      .endLoan 2, .release 2 9] = none := by decide

theorem move_and_release_admitted : (run initial
    [.root 1 4 .exclusive .heap 9, .move 1 2, .endLoan 2, .release 2 9]).isSome = true := by decide

theorem moved_from_access_refused : run initial
    [.root 1 4 .exclusive .heap 9, .move 1 2, .access 1 ⟨1, 0, 4⟩ false] = none := by decide

/-- An input whose storage is released and then replaced by a fresh allocation
of the same family. -/
def growPlan (family : Nat) : List Action :=
  [.root 1 1 .exclusive .input 0, .vacate 1 9, .root 2 8 .exclusive .heap 9, .replace 1 2 family]

theorem vacate_then_replace_admitted : (run initial (growPlan 9)).isSome = true := by decide

theorem replace_other_family_than_released_refused : run initial (growPlan 8) = none := by decide

/-- Storage is replaced only after its old storage was released. -/
theorem replace_without_release_refused : run initial
    [.root 1 1 .exclusive .input 0, .root 2 8 .exclusive .heap 9, .replace 1 2 9] = none := by decide

/-- Storage released to a call that always releases it never comes back. -/
theorem restore_after_release_refused : run initial
    [.root 1 1 .exclusive .input 0, .vacate 1 9, .restore 1] = none := by decide

theorem vacate_twice_refused : run initial
    [.root 1 1 .exclusive .input 0, .vacate 1 9, .vacate 1 9] = none := by decide

/-- Only an input's storage is released to be replaced. -/
theorem vacate_local_refused : run initial
    [.root 1 8 .exclusive .local 0, .vacate 1 9] = none := by decide

theorem vacate_under_live_borrow_refused : run initial
    [.root 1 1 .exclusive .input 0, .borrow 2 1 ⟨1, 0, 1⟩ .shared, .vacate 1 9] = none := by decide

/-- A null owner ends without a release, once its loan has ended. -/
theorem null_owner_admitted : (run initial
    [.root 1 4 .exclusive .heap 9, .endLoan 1, .nullOwner 1 9]).isSome = true := by decide

theorem null_owner_still_lent_refused : run initial
    [.root 1 4 .exclusive .heap 9, .nullOwner 1 9] = none := by decide

theorem null_owner_other_family_refused : run initial
    [.root 1 4 .exclusive .heap 9, .endLoan 1, .nullOwner 1 8] = none := by decide

end Controls

end Mettapedia.Ownership
