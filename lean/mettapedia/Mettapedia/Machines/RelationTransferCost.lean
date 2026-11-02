import Mathlib.Tactic

/-!
# Rows a relation takes over, moved in passes: at most five reads per row
# counted

A head that reaches its relation's threshold kept the rows it had counted as
rows, so every later read of the head walked both forms, and the rows stayed
beside the relation: BI 12 at scale 0.1 peaked at 255 MB, 200 MB with the
rows moved in.  Now a
head's counted rows become pending when it takes its relation.  Once the
pending rows are at least half the live rows, one pass reads every row and
moves the pending ones a relation can take into it.  The pending count is
an estimate from above: a pending row removed meanwhile is not subtracted,
and a pass may move fewer rows than it counts (a multiset's second copy, an
open fact, a fact gone); it is cleared by the pass.

The model: the live rows, the pending estimate, the rows counted at
promotions, and the work of passes (the rows read plus the rows moved).
This file proves:
* `dual_bound`: whenever a promotion leaves rows pending, they are fewer
  than half the live rows;
* `work_bound`: the work of every pass of any run stays within five times
  the rows counted at promotions.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationTransferCost

structure St where
  rows : Nat
  pending : Nat
  counted : Nat
  work : Nat

inductive Op
  /-- A row no relation takes. -/
  | add
  /-- A head takes its relation: `c` of the live rows were counted toward
  it; a pass, if one runs, moves `m` rows. -/
  | promote (c m : Nat)
  /-- A row leaves. -/
  | remove

/-- A pass, when the pending rows are at least half the live rows: it reads
the rows, moves at most the pending ones, and settles the marks the moved
rows leave, reading the rows once more: a space left marked would take the
trie for its next cursor, which every later row then fills. -/
def pass (s : St) (m : Nat) : St :=
  if s.pending ≠ 0 ∧ s.rows ≤ 2 * s.pending then
    ⟨s.rows - min m s.pending, 0, s.counted,
      s.work + s.rows + min m s.pending + s.rows⟩
  else s

def step (s : St) : Op → St
  | .add => ⟨s.rows + 1, s.pending, s.counted, s.work⟩
  | .promote c m =>
    pass ⟨s.rows, min s.rows (s.pending + c), s.counted + c, s.work⟩ m
  | .remove => ⟨s.rows - 1, min (s.rows - 1) s.pending, s.counted, s.work⟩

def run (s : St) : List Op → St
  | [] => s
  | op :: ops => run (step s op) ops

/-- The invariant: the pending estimate is within the live rows, and the
work, with five for each pending row, stays within five times the counted
rows: a pass reads at most twice its pending rows, moves at most them, and
settles at most twice them. -/
def Inv (s : St) : Prop :=
  s.pending ≤ s.rows ∧ s.pending ≤ s.counted ∧ s.work + 5 * s.pending ≤ 5 * s.counted

theorem step_inv (s : St) (op : Op) (inv : Inv s) : Inv (step s op) := by
  obtain ⟨within, est, paid⟩ := inv
  unfold Inv
  cases op with
  | add => simp only [step]; omega
  | promote c m =>
    simp only [step, pass]
    split
    · simp only [min_def] at *
      split_ifs at * <;> omega
    · simp only [min_def] at *
      split_ifs at * <;> omega
  | remove =>
    simp only [step, min_def]
    split_ifs <;> omega

theorem run_inv (ops : List Op) : ∀ s, Inv s → Inv (run s ops) := by
  induction ops with
  | nil => intro s inv; exact inv
  | cons op ops ih =>
    intro s inv
    exact ih (step s op) (step_inv s op inv)

/-- The work of every pass of any run from no rows stays within five times
the rows counted at promotions. -/
theorem work_bound (ops : List Op) :
    (run ⟨0, 0, 0, 0⟩ ops).work ≤ 5 * (run ⟨0, 0, 0, 0⟩ ops).counted := by
  obtain ⟨_, _, paid⟩ := run_inv ops ⟨0, 0, 0, 0⟩ (by unfold Inv; simp)
  omega

/-- Whenever a promotion leaves rows pending, they are fewer than half the
live rows: readers walk both forms for less than half the rows. -/
theorem dual_bound (s : St) (c m : Nat) :
    let t := step s (.promote c m)
    t.pending = 0 ∨ 2 * t.pending < t.rows := by
  simp only [step, pass]
  split
  · left; rfl
  · rename_i h
    simp only [min_def] at h ⊢
    split_ifs at h ⊢ <;> omega

/-- A head's 15 counted rows beside 5 others: its promotion moves them at
once, reading the 20 rows and settling them. -/
example :
    let s := step ⟨20, 0, 0, 0⟩ (.promote 15 15)
    s.rows = 5 ∧ s.pending = 0 ∧ s.work = 55 := by
  decide

/-- A head of 4,095 counted rows beside a million rows no relation takes:
its promotion leaves them pending, readers walking both forms, rather than
reading a million rows to move four thousand. -/
example :
    let s := step ⟨1004095, 0, 0, 0⟩ (.promote 4095 4095)
    s.pending = 4095 ∧ s.work = 0 := by
  decide

end Mettapedia.Machines.RelationTransferCost
