import Mettapedia.Machines.StableNumberCompaction
import Mettapedia.Machines.RelationBagTransfer

/-!
# Original occurrence coordinates through row take-over

Successful offers emit strictly increasing original logical positions. Removing
those positions is proved equal to the Boolean-mask specification, including
when target give-back appends new rows. A second worker traverses a physical
live mask, advancing the logical coordinate only at a live row. Its decoded
result agrees with logical removal; settling physical marks preserves that
result. Equal values do not identify equal occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationTransferCoordinates

variable {Fact : Type}

def positions : Nat → List Bool → List Nat
  | _, [] => []
  | start, selected :: rest =>
      if selected then start :: positions (start + 1) rest else positions (start + 1) rest

theorem positions_bounds (start : Nat) (mask : List Bool) (position : Nat)
    (member : position ∈ positions start mask) : start ≤ position ∧ position < start + mask.length := by
  induction mask generalizing start with
  | nil => simp [positions] at member
  | cons selected rest ih =>
      cases selected
      · have bound := ih (start + 1) (by simpa [positions] using member)
        simp only [List.length_cons]
        omega
      · have choice : position = start ∨ position ∈ positions (start + 1) rest := by
          simpa [positions] using member
        rcases choice with rfl | member
        · simp
        · have bound := ih (start + 1) member
          simp only [List.length_cons]
          omega

theorem positions_strict (start : Nat) (mask : List Bool) :
    (positions start mask).Pairwise (· < ·) := by
  induction mask generalizing start with
  | nil => simp [positions]
  | cons selected rest ih =>
      cases selected
      · exact ih (start + 1)
      · simp only [positions, ↓reduceIte, List.pairwise_cons]
        exact ⟨fun index member => (positions_bounds (start + 1) rest index member).1, ih (start + 1)⟩

theorem positions_length (start : Nat) (mask : List Bool) :
    (positions start mask).length = mask.count true := by
  induction mask generalizing start with
  | nil => rfl
  | cons selected rest ih => cases selected <;> simp [positions, ih]

/-- Reference deletion by original coordinates, never by the shrinking suffix's
current position. -/
def remove (selected : List Nat) : Nat → List Fact → List Fact
  | _, [] => []
  | start, fact :: rest =>
      if start ∈ selected then remove selected (start + 1) rest
      else fact :: remove selected (start + 1) rest

theorem remove_agrees (first second : List Nat) (start : Nat) (rows : List Fact)
    (same : ∀ index, start ≤ index → (index ∈ first ↔ index ∈ second)) :
    remove first start rows = remove second start rows := by
  induction rows generalizing start with
  | nil => rfl
  | cons fact rest ih =>
      have tail := ih (start + 1) (fun index bound => same index (by omega))
      simp only [remove, same start (Nat.le_refl start), tail]

theorem remove_old_position (position start : Nat) (selected : List Nat) (rows : List Fact)
    (earlier : position < start) : remove (position :: selected) start rows = remove selected start rows := by
  apply remove_agrees
  intro index bound
  have apart : index ≠ position := by omega
  simp [apart]

theorem remove_positions (start : Nat) (mask : List Bool) (rows : List Fact)
    (size : mask.length = rows.length) :
    remove (positions start mask) start rows = RelationBagTransfer.retained rows mask := by
  induction mask generalizing start rows with
  | nil => have empty : rows = [] := List.eq_nil_of_length_eq_zero size.symm; subst rows; rfl
  | cons selected rest ih =>
      cases rows with
      | nil => simp at size
      | cons fact rows =>
          have tail := ih (start + 1) rows (by simpa using size)
          have absent : start ∉ positions (start + 1) rest := by
            intro member
            have bound := (positions_bounds (start + 1) rest start member).1
            omega
          cases selected
          · simpa [positions, remove, RelationBagTransfer.retained, absent] using congrArg (fact :: ·) tail
          · simpa only [positions, Bool.true_eq, ↓reduceIte, remove, List.mem_cons_self,
              RelationBagTransfer.retained, remove_old_position start (start + 1) _ rows (by omega)] using tail

theorem remove_append (selected : List Nat) (start : Nat) (rows later : List Fact) :
    remove selected start (rows ++ later) =
      remove selected start rows ++ remove selected (start + rows.length) later := by
  induction rows generalizing start with
  | nil => simp [remove]
  | cons fact rows ih =>
      by_cases hit : start ∈ selected <;>
        simp [remove, hit, ih, Nat.add_comm, Nat.add_left_comm]

theorem remove_past_end (selected : List Nat) (start : Nat) (rows : List Fact)
    (before : ∀ index ∈ selected, index < start) : remove selected start rows = rows := by
  induction rows generalizing start with
  | nil => rfl
  | cons fact rows ih =>
      have absent : start ∉ selected := by intro member; exact Nat.lt_irrefl start (before start member)
      have tail := ih (start + 1) (by intro index member; have := before index member; omega)
      simp [remove, absent, tail]

theorem give_back_suffix_kept (start : Nat) (mask : List Bool) (rows later : List Fact)
    (size : mask.length = rows.length) :
    remove (positions start mask) start (rows ++ later) =
      RelationBagTransfer.retained rows mask ++ later := by
  rw [remove_append, remove_positions start mask rows size]
  rw [remove_past_end]
  intro index member
  simpa [size] using (positions_bounds start mask index member).2

/-- Existing holes do not consume a logical position. -/
def mark (selected : List Nat) : Nat → List Bool → List Bool
  | _, [] => []
  | logical, false :: rest => false :: mark selected logical rest
  | logical, true :: rest => decide (logical ∉ selected) :: mark selected (logical + 1) rest

theorem mark_length (selected : List Nat) (logical : Nat) (alive : List Bool) :
    (mark selected logical alive).length = alive.length := by
  induction alive generalizing logical with
  | nil => rfl
  | cons live rest ih => cases live <;> simp [mark, ih]

theorem mark_refines (selected : List Nat) (logical : Nat) (alive : List Bool) (physical : List Fact)
    (size : alive.length = physical.length) :
    StableNumberCompaction.pack (mark selected logical alive) physical =
      remove selected logical (StableNumberCompaction.pack alive physical) := by
  induction alive generalizing logical physical with
  | nil => simp [mark, StableNumberCompaction.pack, remove]
  | cons live rest ih =>
      cases physical with
      | nil => simp at size
      | cons fact physical =>
          have size_tail : rest.length = physical.length := by simpa using size
          cases live
          · simpa [mark, StableNumberCompaction.pack] using ih logical physical size_tail
          · by_cases selected_here : logical ∈ selected <;>
              simp [mark, StableNumberCompaction.pack, selected_here, remove,
                ih (logical + 1) physical size_tail]

theorem settling_keeps_readout (rows : List Fact) :
    StableNumberCompaction.pack (List.replicate rows.length true) rows = rows := by
  induction rows with
  | nil => rfl
  | cons fact rows ih => simp [List.replicate_succ, StableNumberCompaction.pack, ih]

theorem original_positions_preserve_takeover_bag [DecidableEq Fact]
    (choose : Nat → Fact → RelationBagTransfer.Action) (before : RelationBagTransfer.Store Fact) :
    let planned := RelationBagTransfer.plan choose 0 before.rows before.target
    ((remove (positions 0 planned.2) 0 (before.rows ++ planned.1.spilled)) : Multiset Fact) +
      (planned.1.dense : Multiset Fact) = before.bag := by
  dsimp
  rw [give_back_suffix_kept 0 _ before.rows _ (RelationBagTransfer.plan_length ..)]
  simpa only [RelationBagTransfer.transfer, RelationBagTransfer.Store.bag, ← Multiset.coe_add,
    add_assoc, add_comm, add_left_comm] using RelationBagTransfer.transfer_bag choose before

theorem physical_marks_preserve_takeover_bag [DecidableEq Fact]
    (choose : Nat → Fact → RelationBagTransfer.Action) (physical : List Fact) (alive : List Bool)
    (size : alive.length = physical.length) (target : RelationBagTransfer.Target Fact) :
    let rows := StableNumberCompaction.pack alive physical
    let planned := RelationBagTransfer.plan choose 0 rows target
    ((StableNumberCompaction.pack (mark (positions 0 planned.2) 0 alive) physical ++
      planned.1.spilled) : Multiset Fact) + (planned.1.dense : Multiset Fact) =
      (RelationBagTransfer.Store.mk rows target).bag := by
  dsimp
  rw [mark_refines _ 0 alive physical size,
    remove_positions 0 _ _ (RelationBagTransfer.plan_length ..)]
  simpa only [RelationBagTransfer.transfer, RelationBagTransfer.Store.bag, ← Multiset.coe_add,
    add_assoc, add_comm, add_left_comm] using
      RelationBagTransfer.transfer_bag choose ⟨StableNumberCompaction.pack alive physical, target⟩

namespace Controls

theorem duplicate_occurrences_have_separate_coordinates :
    positions 0 [true, false, true] = [0, 2] ∧
    remove [0, 2] 0 ([7, 7, 9] : List Nat) = [7] := by decide

theorem preexisting_marks_do_not_shift_logical_targets :
    mark [1] 0 [false, true, false, true, true] = [false, true, false, false, true] ∧
    StableNumberCompaction.pack (mark [1] 0 [false, true, false, true, true])
      [99, 7, 98, 9, 7] = [7, 7] := by decide

theorem physical_indices_are_not_logical_indices :
    remove [1] 0 ([99, 7, 98, 9, 7] : List Nat) = [99, 98, 9, 7] ∧
    remove [1] 0 ([7, 9, 7] : List Nat) = [7, 7] := by decide

theorem give_back_is_not_deleted_as_an_old_occurrence :
    remove (positions 0 [true, false, true]) 0 ([7, 7, 9] ++ [7] : List Nat) = [7, 7] := by decide

end Controls
end Mettapedia.Machines.RelationTransferCoordinates
