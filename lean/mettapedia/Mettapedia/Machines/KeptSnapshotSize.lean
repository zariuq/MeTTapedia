import Mathlib.Tactic

/-!
# A cursor's facts of a relation, held at their size

An occurrence cursor over a relation's facts holds the facts the pattern
selected, their columns and a record slot each.  The columns grew by doubling
from room for 16 facts, so a cursor of `k` facts of `a` columns held the room
of the least power-of-two multiple of 16 at least `k`; a recursion keeping a
cursor at every level held that room at every level.  Gathered first and held
in one allocation of their size, the facts take `k * (a + 1)` cells.

This file proves:
* `grown_ge`: the doubling rule's room is at least the facts and at least 16;
* `exact_le_doubling`: the exact cells never exceed the doubling rule's cells;
* `exact_saves_below_16`: for fewer than 16 facts they fall short of them by
  at least `(16 - k) * a`;
* `levels_exact`: `d` levels holding cursors of `k` facts hold `d` times the
  exact cells.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.KeptSnapshotSize

/-- Room by doubling from 16, as a function of the facts held. -/
def grown : Nat → Nat
  | 0 => 16
  | k + 1 => if k + 1 ≤ grown k then grown k else 2 * grown k

/-- The cells a cursor of `k` facts of `a` columns held: the doubled room of
columns plus a record slot each. -/
def doublingCells (a k : Nat) : Nat := grown k * a + k

/-- The cells held at their size. -/
def exactCells (a k : Nat) : Nat := k * (a + 1)

theorem grown_ge (k : Nat) : k ≤ grown k ∧ 16 ≤ grown k := by
  induction k with
  | zero => simp [grown]
  | succ k ih =>
    obtain ⟨hk, h16⟩ := ih
    simp only [grown]
    split <;> omega

theorem exact_le_doubling (a k : Nat) : exactCells a k ≤ doublingCells a k := by
  obtain ⟨hk, _⟩ := grown_ge k
  unfold exactCells doublingCells
  have := Nat.mul_le_mul_right a hk
  nlinarith

theorem exact_saves_below_16 (a k : Nat) (few : k < 16) :
    exactCells a k + (16 - k) * a ≤ doublingCells a k := by
  obtain ⟨_, h16⟩ := grown_ge k
  unfold exactCells doublingCells
  have h : 16 * a ≤ grown k * a := Nat.mul_le_mul_right a h16
  have e : (16 - k) * a + k * a = 16 * a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel few.le]
  nlinarith

theorem levels_exact (a k d : Nat) :
    (List.replicate d (exactCells a k)).sum = d * (k * (a + 1)) := by
  simp [exactCells]

/-- Five facts of two holes: 15 cells held at their size against 37. -/
example : exactCells 2 5 = 15 ∧ doublingCells 2 5 = 37 := by decide

/-- Past 16 facts the doubling rule's room is the next power of two: 17
facts of two holes held room for 32. -/
example : grown 17 = 32 := by decide

end Mettapedia.Machines.KeptSnapshotSize
