import Mettapedia.Machines.SuffixViewCopy

/-!
# Transferring a bounded history into a smaller store

The input is in chronological order. Saving a smaller history must retain its
newest suffix, rather than take a prefix of the already bounded input. These
laws apply to terminal panes, retained logs and revision windows. Physical ring
indexing is stated separately; no C implementation refinement is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundedHistoryTransfer

variable {α : Type*}

/-- The copying algorithm: skip every row preceding the retained suffix. -/
def save (capacity : Nat) (source : List α) : List α :=
  source.drop (source.length - min capacity source.length)

theorem save_eq_view (capacity : Nat) (source : List α) :
    save capacity source = SuffixViewCopy.view source capacity := by
  unfold save SuffixViewCopy.view
  congr 1
  omega

theorem saved_length (capacity : Nat) (source : List α) :
    (save capacity source).length = min capacity source.length := by
  rw [save_eq_view, SuffixViewCopy.view_length]

/-- Reducing capacity in stages retains exactly the same newest rows. -/
theorem transfer_composes (history : List α) {small large : Nat}
    (bound : small ≤ large) :
    save small (save large history) = save small history := by
  simp only [save_eq_view]
  exact SuffixViewCopy.view_view bound

/-- An entire capacity-sized newest suffix survives regardless of older rows. -/
theorem newest_suffix_survives (older recent : List α) :
    save recent.length (older ++ recent) = recent := by
  rw [save_eq_view]
  simp [SuffixViewCopy.view, List.length_append]

/-- The last copied slot is the ring's latest published slot. -/
theorem last_ring_index (write capacity keep : Nat) (nonempty : 0 < keep)
    (bounded : keep ≤ capacity) :
    (write + capacity - keep + (keep - 1)) % capacity =
      (write + capacity - 1) % capacity := by
  congr 1
  omega

theorem spindle_transfer (history : List α) :
    save 64 (save 1024 history) = save 64 history :=
  transfer_composes history (by decide)

/-- A 65th line is lost by prefix copying, but retained by suffix copying. -/
theorem original_prefix_loses_latest :
    (List.range 65).take 64 ≠ save 64 (List.range 65) := by
  decide

theorem positive_small_history : save 64 ([1, 2, 3] : List Nat) = [1, 2, 3] := by
  decide

theorem negative_oldest_prefix : save 2 ([1, 2, 3] : List Nat) ≠ [1, 2] := by
  decide

end Mettapedia.Machines.BoundedHistoryTransfer
