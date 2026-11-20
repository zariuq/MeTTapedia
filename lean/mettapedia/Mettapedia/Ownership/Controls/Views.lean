import Mettapedia.Ownership.Views
import Mettapedia.Ownership.Controls.Interface

/-!
# Controls: views

Examples admitted and refused.
-/

set_option autoImplicit false

namespace Mettapedia.Ownership

open Mettapedia.Machines.CMemory.Borrowing

namespace ViewControls

open Controls

theorem stack_view_cannot_escape : run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .endLoan 1] = none := by decide

theorem vector_cannot_release_under_view : run initial
    [.root 1 16 .exclusive .heap 9, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .endLoan 1, .release 1 9] = none := by decide

theorem arena_cannot_reset_under_view : run initial
    [.root 1 4096 .exclusive .local 0, .borrow 2 1 ⟨1, 128, 64⟩ .shared,
      .endLoan 1] = none := by decide

theorem cloned_read_views_allowed : (run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .borrow 3 2 ⟨1, 0, 8⟩ .shared,
      .view 2 ⟨1, 0, 8⟩ 8 false, .view 3 ⟨1, 0, 8⟩ 8 false]).isSome = true := by decide

theorem exclusive_copy_suspends_source : run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .exclusive,
      .borrow 3 2 ⟨1, 0, 8⟩ .exclusive, .access 2 ⟨1, 0, 1⟩ true] = none := by decide

theorem disjoint_mutable_slices_allowed : (run initial
    [.root 1 16 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .exclusive,
      .borrow 3 1 ⟨1, 8, 8⟩ .exclusive,
      .view 2 ⟨1, 0, 8⟩ 8 true, .view 3 ⟨1, 8, 8⟩ 8 true]).isSome = true := by decide

theorem forged_length_refused : run initial
    [.root 1 8 .exclusive .local 0, .view 1 ⟨1, 0, 8⟩ 9 false] = none := by decide

theorem forged_footprint_refused : run initial
    [.root 1 8 .exclusive .local 0, .view 1 ⟨1, 0, 9⟩ 9 false] = none := by decide

theorem dead_view_refused : run initial
    [.root 1 8 .exclusive .local 0, .endLoan 1, .view 1 ⟨1, 0, 8⟩ 8 false] = none := by decide

theorem narrowed_view_uses_new_bound : (run initial
    [.root 1 8 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .restrict 2 ⟨1, 0, 4⟩, .access 2 ⟨1, 3, 1⟩ false]).isSome = true := by decide

theorem old_bound_cannot_survive_narrowing : run initial
    [.root 1 8 .exclusive .local 0, .borrow 2 1 ⟨1, 0, 8⟩ .shared,
      .restrict 2 ⟨1, 0, 4⟩, .access 2 ⟨1, 4, 1⟩ false] = none := by decide

theorem restriction_cannot_shrink_release_authority : run initial
    [.root 1 8 .exclusive .heap 9, .restrict 1 ⟨1, 0, 4⟩] = none := by decide

theorem empty_view_has_no_index : ¬∃ index : Nat, index < (0 : Nat) := by omega

end ViewControls

end Mettapedia.Ownership
