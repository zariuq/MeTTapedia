import Mettapedia.Machines.Cursor.ReaderResidualIndex

/-!
# Residual index controls with duplicate payloads and unique occurrence IDs
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ReaderResidualIndex.Controls

open StampedSnapshots StampedSnapshotsIndex

def original : Store (Tuple Nat) :=
  add (add (add StampedSnapshots.empty [1, 7]) [1, 7]) [1, 9]

def originalIndex : Index Nat := load original original.next empty
def entry : Reader := start original
def advanced : Reader := (step original entry).2
def written : Store (Tuple Nat) := remove (add original [1, 11]) 1
def rebuilt : Index Nat := load written written.next empty

theorem advanced_reader_position : advanced = ⟨3, 3, 1⟩ := by decide

/-- Equal payloads do not allow the delivered first occurrence to replay. -/
theorem residual_has_second_duplicate_only :
    chainResidual original originalIndex advanced 0 1 = [(1, [1, 7]), (2, [1, 9])] ∧
      bitResidual original originalIndex advanced 0 1 = [(1, [1, 7]), (2, [1, 9])] := by decide

theorem restarting_replays_unique_id :
    chainQuery original originalIndex advanced 0 1 =
      [(0, [1, 7]), (1, [1, 7]), (2, [1, 9])] ∧
      chainQuery original originalIndex advanced 0 1 ≠
        chainResidual original originalIndex advanced 0 1 := by decide

theorem rebuild_after_writes_keeps_residual :
    chainResidual original originalIndex advanced 0 1 =
      bitResidual written rebuilt advanced 0 1 ∧
      bitResidual written rebuilt advanced 0 1 = [(1, [1, 7]), (2, [1, 9])] := by decide

def adopted : Reader := { start written with position := advanced.position }

/-- Keeping only the position while replacing time/ceiling adopts a different
query. The old retired row is lost and the new row wrongly enters its place. -/
theorem adopting_current_view_changes_residual :
    bitResidual written rebuilt adopted 0 1 = [(2, [1, 9]), (3, [1, 11])] ∧
      bitResidual written rebuilt adopted 0 1 ≠ bitResidual written rebuilt advanced 0 1 := by decide

theorem past_ceiling_is_empty :
    chainResidual original originalIndex { entry with position := 8 } 0 1 = [] ∧
      bitResidual original originalIndex { entry with position := 8 } 0 1 = [] := by decide

theorem proof_driven_rebuild_transfer :
    chainResidual original originalIndex advanced 0 1 = bitResidual written rebuilt advanced 0 1 := by
  apply transfer_after_writes original originalIndex
    (valid_load original original.next empty (valid_empty original)) advanced
      (by decide) (by constructor <;> decide) [1, 11] 1 0 1 rebuilt
  · exact valid_load written written.next empty (valid_empty written)
  · exact Nat.le_trans (by decide : advanced.ceiling ≤ written.next)
      (by simp only [rebuilt, load_all_covered]; exact le_rfl)

#print axioms chain_residual_exact
#print axioms bit_residual_exact
#print axioms transfer_preserves_residual
#print axioms transfer_after_writes
#print axioms no_replay

end Mettapedia.Machines.Cursor.ReaderResidualIndex.Controls
