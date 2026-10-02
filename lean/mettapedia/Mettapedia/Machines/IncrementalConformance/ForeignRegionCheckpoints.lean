import Mettapedia.Machines.ConstraintPropagation

/-!
# Retained-region checkpoint compaction

The native solver keeps nested foreign frames. A frame older than every retained
binding checkpoint can no longer be rolled back, but cannot be physically closed
while a younger live frame depends on it. Such frames become anchors.

The marking rule uses the binding service's canonical `keptUpTo` and
`keptPosition`. Unlike its undo log, this representation retains anchors with
no rollback mark. We prove that exactly the same saved states are restored at
every retained checkpoint before and after compaction. State includes both the
solver graph and its variable-key catalogue. Physical frame lifetime and closing
anchors after younger frames disappear are qualified by the native gate.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IncrementalConformance.ForeignRegionCheckpoints

open Mettapedia.Machines.ConstraintPropagation

variable {State : Type}

def renamed (kept : List Nat) (mark : Nat) : Option Nat :=
  if keptUpTo kept mark = 0 then none else some (keptUpTo kept mark - 1)

/-- Every frame stays in physical order; `none` is a non-rewindable anchor. -/
def compact (kept : List Nat) (frames : List (Nat × State)) : List (Option Nat × State) :=
  frames.map fun frame => (renamed kept frame.1, frame.2)

/-- Original checkpoints select saved states by the old binding-trail mark. -/
def originalSnapshots (mark : Nat) (frames : List (Nat × State)) : List State :=
  (frames.filter fun frame => mark ≤ frame.1).map Prod.snd

/-- Compacted checkpoints skip anchors and use the new binding-trail position. -/
def retainedSnapshots (mark : Nat) : List (Option Nat × State) → List State
  | [] => []
  | (none, _) :: rest => retainedSnapshots mark rest
  | (some position, state) :: rest =>
      if mark ≤ position then state :: retainedSnapshots mark rest
      else retainedSnapshots mark rest

theorem snapshots_compaction (kept : List Nat) (checkpoint : Nat)
    (present : checkpoint ∈ kept) (frames : List (Nat × State)) :
    retainedSnapshots (keptPosition kept checkpoint) (compact kept frames) =
      originalSnapshots checkpoint frames := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have criterion := rebase_undoes_iff (kept := kept) (t := frame.1) present
      by_cases anchor : keptUpTo kept frame.1 = 0
      · have older : ¬ checkpoint ≤ frame.1 := by
          intro selected
          exact (criterion.mpr selected).1 anchor
        simpa [compact, renamed, anchor, retainedSnapshots, originalSnapshots,
          older] using ih
      · by_cases selected : checkpoint ≤ frame.1
        · have selects := (criterion.mpr selected).2
          simpa [compact, renamed, anchor, retainedSnapshots, originalSnapshots,
            selects, selected] using congrArg (List.cons frame.2) ih
        · have skips : ¬ keptPosition kept checkpoint ≤ keptUpTo kept frame.1 - 1 := by
            intro selects
            exact selected (criterion.mp ⟨anchor, selects⟩)
          simpa [compact, renamed, anchor, retainedSnapshots, originalSnapshots,
            skips, selected] using ih

/-- Checkpoints are stored newest first. Restoring them in order ends at the
oldest selected snapshot, including both the solver and its catalogue. -/
def restore (snapshots : List State) (current : State) : State :=
  snapshots.foldl (fun _ saved => saved) current

theorem rollback_compaction (kept : List Nat) (checkpoint : Nat)
    (present : checkpoint ∈ kept) (frames : List (Nat × State)) (current : State) :
    restore (retainedSnapshots (keptPosition kept checkpoint) (compact kept frames)) current =
      restore (originalSnapshots checkpoint frames) current := by
  rw [snapshots_compaction kept checkpoint present]

/-- Greatest retained absolute mark at or below the operation mark. Zero
stands for a discarded prefix unless zero itself is a live checkpoint. -/
def floorMark (kept : List Nat) (mark : Nat) : Nat :=
  match kept with
  | [] => 0
  | head :: rest =>
      if head ≤ mark then max head (floorMark rest mark) else floorMark rest mark

theorem floorMark_le (kept : List Nat) (mark : Nat) : floorMark kept mark ≤ mark := by
  induction kept with
  | nil => exact Nat.zero_le _
  | cons head rest ih =>
      by_cases h : head ≤ mark
      · simpa [floorMark, h] using max_le h ih
      · simpa [floorMark, h] using ih

theorem member_le_floorMark (kept : List Nat) (checkpoint mark : Nat)
    (present : checkpoint ∈ kept) (before : checkpoint ≤ mark) :
    checkpoint ≤ floorMark kept mark := by
  induction kept with
  | nil => simp at present
  | cons head rest ih =>
      rcases List.mem_cons.mp present with same | tail
      · subst head
        simp only [floorMark, if_pos before]
        exact Nat.le_max_left _ _
      · have selected := ih tail
        by_cases h : head ≤ mark
        · simpa [floorMark, h] using selected.trans (Nat.le_max_right head _)
        · simpa [floorMark, h] using selected

theorem floorMark_undoes_iff (kept : List Nat) (checkpoint mark : Nat)
    (present : checkpoint ∈ kept) :
    checkpoint ≤ floorMark kept mark ↔ checkpoint ≤ mark :=
  ⟨fun h => h.trans (floorMark_le kept mark), member_le_floorMark kept checkpoint mark present⟩

def absoluteFrontier (kept : List Nat) (frames : List (Nat × State)) : List (Nat × State) :=
  frames.map fun frame => (floorMark kept frame.1, frame.2)

/-- Pruning retains the old numeric binding marks; no native binding-store
compaction is needed to use the same live rollback horizon. -/
theorem absolute_frontier_snapshots (kept : List Nat) (checkpoint : Nat)
    (present : checkpoint ∈ kept) (frames : List (Nat × State)) :
    originalSnapshots checkpoint (absoluteFrontier kept frames) =
      originalSnapshots checkpoint frames := by
  induction frames with
  | nil => rfl
  | cons frame rest ih =>
      have criterion := floorMark_undoes_iff kept checkpoint frame.1 present
      by_cases selected : checkpoint ≤ frame.1
      · have rounded := criterion.mpr selected
        simpa [originalSnapshots, absoluteFrontier, rounded, selected] using
          congrArg (List.cons frame.2) ih
      · have rounded : ¬ checkpoint ≤ floorMark kept frame.1 :=
          fun h => selected (criterion.mp h)
        simpa [originalSnapshots, absoluteFrontier, rounded, selected] using ih

theorem absolute_frontier_rollback (kept : List Nat) (checkpoint : Nat)
    (present : checkpoint ∈ kept) (frames : List (Nat × State)) (current : State) :
    restore (originalSnapshots checkpoint (absoluteFrontier kept frames)) current =
      restore (originalSnapshots checkpoint frames) current := by
  rw [absolute_frontier_snapshots kept checkpoint present]

/-- Within one rounded horizon, only its oldest pre-state can be the final
restore. The native ledger is oldest-first, while this model is newest-first. -/
theorem adjacent_same_horizon (checkpoint mark : Nat) (newer older : State)
    (rest : List (Nat × State)) (current : State) :
    restore (originalSnapshots checkpoint ((mark, newer) :: (mark, older) :: rest)) current =
      restore (originalSnapshots checkpoint ((mark, older) :: rest)) current := by
  by_cases h : checkpoint ≤ mark <;>
    simp [originalSnapshots, restore, h]

example : floorMark [10, 20] 17 = 10 := by decide

/-- Coalescing must retain the oldest pre-state, not the newest one. -/
example : restore (originalSnapshots 10 [(10, 7), (10, 3)]) 9 = 3 ∧
    restore (originalSnapshots 10 [(10, 7)]) 9 = 7 := by decide

example : compact [2, 4] [(4, 300), (3, 200), (2, 100), (1, 0)] =
    [(some 1, 300), (some 0, 200), (some 0, 100), (none, 0)] := by decide

example : restore (retainedSnapshots 1
    (compact [2, 4] [(4, 300), (3, 200), (2, 100), (1, 0)])) 400 = 300 := by decide

example : restore (retainedSnapshots 0
    (compact [2, 4] [(4, 300), (3, 200), (2, 100), (1, 0)])) 400 = 100 := by decide

/-- Rounding an intermediate mark upward rewinds a state that should survive. -/
example : restore (retainedSnapshots 1 [(some 1, 300), (some 1, 200), (some 0, 100)]) 400 = 200 ∧
    restore (originalSnapshots 4 [(4, 300), (3, 200), (2, 100)]) 400 = 300 := by decide

end Mettapedia.Machines.IncrementalConformance.ForeignRegionCheckpoints
