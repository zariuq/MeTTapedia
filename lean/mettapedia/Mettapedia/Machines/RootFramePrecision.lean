import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Precision accounting for a registered root chain

A flag records whether a registered frame has enumerated every suspended live
slot. The reference admission scans the ancestors of the current frame. A
maintained obstacle count makes the same decision without rescanning the chain.
The laws cover insertion, arbitrary older-frame retirement and precision changes.
They establish the metadata invariant, not discovery of a runtime's live slots.
-/

namespace Mettapedia.Machines.RootFramePrecision

def obstacle (precise : Bool) : Nat := if precise then 0 else 1

def count : List Bool → Nat
  | [] => 0
  | precise :: rest => obstacle precise + count rest

/-- Independent reference scan; the current frame supplies its own live slots. -/
def scan : List Bool → Bool
  | [] => false
  | _ :: ancestors => ancestors.all id

/-- Constant-time admission from the maintained count and the current flag. -/
def counted (marks : List Bool) (obstacles : Nat) : Bool :=
  match marks with
  | [] => false
  | current :: _ => obstacles == obstacle current

theorem count_append (left suffix : List Bool) :
    count (left ++ suffix) = count left + count suffix := by
  induction left with
  | nil => simp [count]
  | cons mark rest ih => simp [count, ih, Nat.add_assoc]

theorem count_zero_iff (marks : List Bool) :
    count marks = 0 ↔ marks.all id = true := by
  induction marks with
  | nil => simp [count]
  | cons mark rest ih =>
      cases mark <;> simp [count, obstacle, ih]

/-- The accumulator judgment agrees with the independent ancestor scan. -/
theorem counted_eq_scan (marks : List Bool) : counted marks (count marks) = scan marks := by
  cases marks with
  | nil => rfl
  | cons current ancestors =>
      apply Bool.eq_iff_iff.mpr
      simp only [counted, count, scan, beq_iff_eq]
      rw [Nat.add_eq_left, count_zero_iff]

/-- Linking a root changes the count by its own precision contribution. -/
theorem link_count (mark : Bool) (marks : List Bool) :
    count (mark :: marks) = count marks + obstacle mark := by
  simp [count, Nat.add_comm]

/-- A precision update can affect any registered ancestor, not only the head.
Subtraction is justified by the old frame's presence in the source chain. -/
theorem set_count (left suffix : List Bool) (old fresh : Bool) :
    count (left ++ fresh :: suffix) =
      count (left ++ old :: suffix) + obstacle fresh - obstacle old := by
  simp only [count_append, count]
  omega

/-- Retiring an arbitrary older root removes its contribution exactly once. -/
theorem retire_count (left suffix : List Bool) (mark : Bool) :
    count (left ++ suffix) = count (left ++ mark :: suffix) - obstacle mark := by
  simp only [count_append, count]
  omega

/-- Setting an already precise frame is idempotent. -/
theorem precise_update_idempotent (left suffix : List Bool) :
    count (left ++ true :: suffix) = count (left ++ true :: suffix) +
      obstacle true - obstacle true := by
  simp [obstacle]

/-- Moving from incomplete roots to complete roots decreases the obstacle
count; restoring the incomplete state puts that same obligation back. -/
theorem suspend_resume_count (left suffix : List Bool) :
    count (left ++ true :: suffix) + 1 = count (left ++ false :: suffix) := by
  simp [count_append, count, obstacle]
  omega

theorem current_incomplete_is_not_an_ancestor_obstacle :
    counted [false, true, true] (count [false, true, true]) = true := by decide

theorem incomplete_ancestor_blocks :
    counted [true, true, false, true] (count [true, true, false, true]) = false := by decide

/-- Forgetting an older root's contribution admits the same unsafe chain. -/
theorem omitted_obstacle_admits_unsafe_chain :
    counted [true, false] 0 = true ∧ scan [true, false] = false := by decide

end Mettapedia.Machines.RootFramePrecision
