import Mettapedia.Machines.Step.StampValidation
import Mettapedia.Machines.Step.StepCost
import Mettapedia.Machines.Step.SeekerJoin

/-!
# Schedules for a runtime, with the answers the models give

Each section is one schedule: a store, a call whose answers are taken one at a
time, writes made between the answers, and what the models of this directory
say the call answers next.  Atoms are numbered; the numbering is given in each
section.  A runtime that implements the step and the reader is expected to give
the answers stated as the law; the answer of a design that breaks the law is
stated beside it.

* `Rebind`: a take whose row was removed is still a firing when another copy
  of the atom is stored (validation by count); stamps alone refuse it.
* `Phantom`: an `absent` condition fails once a matching row is added, though
  every row of the branch's footprint is live.
* `ReadRemoved`: a reads-only branch whose row was removed is an answer of the
  entry view and is not a firing now: the two readings of a read.
* `TakeRemoved`, `TwoTakers`: a take refuses a row that died after the reader
  entered, and two readers that take never deliver one row twice.
* `Churn`: a reader past its first answer yields the rest of its entry view
  after a removal and an insertion.
* `Triangle`: a join resumed after a write yields the triangles of the entry
  relations; the relations as they are after the write hold one more.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.Fixtures

namespace Rebind

open StampValidation Cursor.StampedSnapshots

/-- Rows `(a 1)`, `(a 2)`, `(tok)`, as the atoms `1`, `2`, `0`. -/
def entry : Store Nat := run [.add 1, .add 2, .add 0] empty

/-- The first branch took the token; the caller stored another. -/
def later : Store Nat := run [.remove 2, .add 0] entry

/-- The second branch: it read the row of `(a 2)` and met the token in row 2. -/
def second : Branch Nat := ⟨[1], [2], fun _ => False, 0, 3⟩

/-- **The law**: the token's row is dead, a token is stored, and the branch is
a firing of the store now; firing it leaves `(a 1)` and `(a 2)`.  A design
that validates by the row's stamp alone refuses the branch. -/
theorem expected :
    ¬ Alive later 2 ∧ (firing later second).Enabled (live later) ∧
      (firing later second).fire (live later) = {1, 2} := by
  refine ⟨?_, ⟨by decide, by decide, fun _ _ h => h⟩, by decide⟩
  rintro ⟨r, found, dead⟩
  have h : later.row 2 = some ⟨0, 3, some 4⟩ := by decide
  rw [h] at found
  cases found
  cases dead

end Rebind

namespace Phantom

open StampValidation Cursor.StampedSnapshots

/-- Rows `(a 1)`, `(a 2)`; the atom `(block)` is `9`. -/
def entry : Store Nat := run [.add 1, .add 2] empty

/-- The caller stored `(block)` after the first answer. -/
def later : Store Nat := run [.add 9] entry

/-- The second branch: it read the row of `(a 2)` and requires `(block)`
absent. -/
def second : Branch Nat := ⟨[1], [], fun a => a = 9, 0, 2⟩

/-- **The law**: the branch's one row is live, the test above the ceiling
fails, and the branch is not a firing now.  A design that looks only at the
rows of the footprint, or at the entry view, fires it. -/
theorem expected :
    Alive later 1 ∧ ¬ NoNewMatch later second ∧ ¬ (firing later second).Enabled (live later) := by
  refine ⟨⟨⟨2, 2, none⟩, by decide, rfl⟩, fun fresh => ?_, fun en => ?_⟩
  · exact fresh 2 ⟨9, 3, none⟩ (le_refl 2) (by decide) rfl rfl
  · exact en.2.2 9 (by decide) rfl

end Phantom

namespace ReadRemoved

open StampValidation Cursor.StampedSnapshots

/-- Rows `(a 1)`, `(a 2)`. -/
def entry : Store Nat := run [.add 1, .add 2] empty

/-- The caller removed `(a 2)` after the first answer. -/
def later : Store Nat := run [.remove 1] entry

/-- The second branch: it only read the row of `(a 2)`. -/
def second : Branch Nat := ⟨[1], [], fun _ => False, 0, 2⟩

/-- **Both readings.**  The row is an answer of the view entered at time `2`,
so a reader that answers as `match` delivers it; it is not a firing of the
store now, so a design that rechecks reads does not. -/
theorem expected :
    atTime later 2 1 = some (1, 2) ∧ ¬ (firing later second).Enabled (live later) ∧
      (firing later second.dropReads).Enabled (live later) := by
  refine ⟨by decide, fun en => ?_, ⟨by decide, by decide, fun _ _ h => h⟩⟩
  have := en.2.1 2 (by decide)
  revert this
  decide

end ReadRemoved

/-- Every key is a candidate. -/
def every : Nat → Prop := fun _ => True

instance : DecidablePred every := fun _ => by
  unfold every
  infer_instance

namespace TakeRemoved

open StepCost Index

/-- Keys `1`, `2` for `(a 1)`, `(a 2)`, entered at time `2`. -/
def two : Index Nat := run [.insert 1, .insert 2] Index.empty

/-- **The law**: the outer call takes `1`; a call the caller makes then, which
enters at time `3`, takes `2`; the outer call, resumed past `1`, finds `2` in
its entry view, refuses it because it is dead now, and delivers nothing more.
A design that does not validate delivers `2` a second time. -/
theorem expected :
    (attempt .take every ⟨.all, 2⟩ two).1 = .fired 1 ∧
      (attempt .take every ⟨.all, 3⟩ (apply (.kill 1) two)).1 = .fired 2 ∧
      (attempt .take every ⟨.gt 1, 2⟩ (apply (.kill 2) (apply (.kill 1) two))).1 = .refused 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [attempt_take_outcome every _ _ 1 (by rw [Seeker.filterSeek_eq_ofFinset]; decide)]
    decide
  · rw [attempt_take_outcome every _ _ 2 (by rw [Seeker.filterSeek_eq_ofFinset]; decide)]
    decide
  · rw [attempt_take_outcome every _ _ 2 (by rw [Seeker.filterSeek_eq_ofFinset]; decide)]
    decide

end TakeRemoved

namespace TwoTakers

open StepCost Index

/-- **The law**: two readers enter at time `2`.  The first takes `1`.  The
second finds `1` in its entry view, refuses it, and takes `2`.  A design that
does not validate delivers `1` to both. -/
theorem expected :
    (attempt .take every ⟨.all, 2⟩ TakeRemoved.two).1 = .fired 1 ∧
      (attempt .take every ⟨.all, 2⟩ (apply (.kill 1) TakeRemoved.two)).1 = .refused 1 ∧
      (attempt .take every ⟨.gt 1, 2⟩ (apply (.kill 1) TakeRemoved.two)).1 = .fired 2 := by
  refine ⟨TakeRemoved.expected.1, ?_, ?_⟩
  · rw [attempt_take_outcome every _ _ 1 (by rw [Seeker.filterSeek_eq_ofFinset]; decide)]
    decide
  · rw [attempt_take_outcome every _ _ 2 (by rw [Seeker.filterSeek_eq_ofFinset]; decide)]
    decide

end TwoTakers

namespace Churn

open Index

/-- Keys `10`, `20`, `30`, entered at time `3`. -/
def jobs : Index Nat := run [.insert 10, .insert 20, .insert 30] Index.empty

/-- **The law**: after `20` is removed and `40` inserted, the reader past `10`
yields `20` and `30`. -/
theorem expected (k : Nat) :
    k ∈ (readerSeeker (run [.kill 20, .insert 40] jobs) 3).drain (.gt 10) ↔ k = 20 ∨ k = 30 := by
  have view : view (run [.kill 20, .insert 40] jobs) 3 = {10, 20, 30} := by decide
  rw [Seeker.mem_drain, readerSeeker_keys, view]
  simp only [Finset.mem_insert, Finset.mem_singleton, Bound.admits_gt]
  omega

/-- A reader that takes its time from the clock yields `30` and `40`: it
misses the removed key and sees the inserted one. -/
theorem current_view (k : Nat) :
    k ∈ (readerSeeker (run [.kill 20, .insert 40] jobs) 5).drain (.gt 10) ↔ k = 30 ∨ k = 40 := by
  have view : view (run [.kill 20, .insert 40] jobs) 5 = {10, 30, 40} := by decide
  rw [Seeker.mem_drain, readerSeeker_keys, view]
  simp only [Finset.mem_insert, Finset.mem_singleton, Bound.admits_gt]
  omega

end Churn

namespace Triangle

open Seeker Seeker.Controls

/-- **The law**: the join of the entry relations holds the triangles
`(0, 1, 2)` and `(0, 1, 3)` and no other. -/
theorem expected (t : Nat ×ₗ Nat ×ₗ Nat) :
    t ∈ (triangle ofFinset R S T).keys ↔
      t = toLex (0, toLex (1, 2)) ∨ t = toLex (0, toLex (1, 3)) :=
  triangle_members t

/-- After `(t 4 6)` is stored, the relations as they then are hold the
triangle `(4, 5, 6)` as well: a join whose legs each read the store when they
are reached answers it; the join of the entry relations does not. -/
theorem current_legs :
    toLex (4, toLex (5, 6)) ∈ (triangle ofFinset R S (insert (4, 6) T)).keys ∧
      toLex (4, toLex (5, 6)) ∉ (triangle ofFinset R S T).keys := by
  constructor
  · exact (mem_triangle_keys ofFinset (fun _ => rfl) R S _ 4 5 6).mpr (by decide)
  · rw [mem_triangle_keys ofFinset (fun _ => rfl)]
    decide

end Triangle

end Mettapedia.Machines.Step.Fixtures
