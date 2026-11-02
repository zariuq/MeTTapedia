import Mathlib.Tactic

/-!
# A relation's numbering: ids released exactly, numbers rebuilt when the
# dead ones pile up

A relation numbers the ids its facts hold and keeps a reference for each.  It
kept every number, and every reference, for as long as it lived: removed
facts left their ids held, so the terms only they named stayed in the term
universe.  Now each number counts the fact columns holding it.  The removal
that takes its count to zero releases the id at once, and the number stays,
dead, for the id to take again.  Once the dead numbers outnumber twice the
slots the facts fill, plus the first room `c₀`, the relation renumbers its
live ids in order and drops the dead.  The room for numbers doubles when full
and is rebuilt at twice the live numbers.

The model: the slots the facts fill (`slots`, a fact of `a` columns filling
`a`), the live and dead numbers, the room, and the work paid: a doubling
copies the numbers, a rebuild reads every slot and number and lays out the
new room.  An operation's choices are clamped to what a relation can do: an
add makes and revives at most `a` numbers, revives only dead ones, and a
removal kills between what the slots left require and what its `a` columns
held.  This file proves:
* `numbers_bound`: the numbers stay within three times the slots plus `c₀`,
  and the room within twice that or `c₀`;
* `work_amortized`: the work of any run stays within `3 a` per operation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.RelationNumberingCost

structure St where
  slots : Nat
  live : Nat
  dead : Nat
  room : Nat
  work : Nat

inductive Op
  /-- A fact enters, making `fresh` numbers and reviving `revived` dead ones. -/
  | add (fresh revived : Nat)
  /-- A fact leaves, and `deaths` numbers lose their last holder. -/
  | remove (deaths : Nat)

/-- The dead numbers an add revives: within its columns and the dead. -/
def revives (a : Nat) (s : St) (r : Nat) : Nat := min (min r a) s.dead

/-- The numbers an add makes, beside those it revives, within its columns. -/
def makes (a : Nat) (s : St) (f r : Nat) : Nat := min f (a - revives a s r)

/-- The numbers a removal kills: at most its columns' and the live, at least
as many as the slots left cannot hold. -/
def kills (a : Nat) (s : St) (k : Nat) : Nat :=
  max (s.live + a - s.slots) (min k (min a s.live))

def step (a c₀ : Nat) (s : St) : Op → St
  | .add f r =>
    if s.live + s.dead + makes a s f r ≤ s.room then
      ⟨s.slots + a, s.live + makes a s f r + revives a s r,
        s.dead - revives a s r, s.room, s.work⟩
    else
      ⟨s.slots + a, s.live + makes a s f r + revives a s r,
        s.dead - revives a s r, 2 * s.room, s.work + (s.live + s.dead)⟩
  | .remove k =>
    if s.slots < a then s
    else if 2 * (s.slots - a) + c₀ < s.dead + kills a s k then
      ⟨s.slots - a, s.live - kills a s k, 0, max c₀ (2 * (s.live - kills a s k)),
        s.work + (s.slots - a) + (s.live - kills a s k) + (s.dead + kills a s k) +
          max c₀ (2 * (s.live - kills a s k))⟩
    else ⟨s.slots - a, s.live - kills a s k, s.dead + kills a s k, s.room, s.work⟩

def run (a c₀ : Nat) (s : St) : List Op → St
  | [] => s
  | op :: ops => run a c₀ (step a c₀ s op) ops

/-- The invariant: every live number has a slot, the dead are within twice
the slots plus `c₀`, the numbers fit the room, and the room is at least `c₀`
and within twice the numbers or `c₀`. -/
def Inv (c₀ : Nat) (s : St) : Prop :=
  s.live ≤ s.slots ∧ s.dead ≤ 2 * s.slots + c₀ ∧ s.live + s.dead ≤ s.room ∧
    c₀ ≤ s.room ∧ s.room ≤ max c₀ (2 * (s.live + s.dead))

theorem step_inv (a c₀ : Nat) (ac : a ≤ c₀) (s : St) (op : Op) (inv : Inv c₀ s) :
    Inv c₀ (step a c₀ s op) := by
  obtain ⟨held, few, fit, floor, roomy⟩ := inv
  cases op with
  | add f r =>
    by_cases h : s.live + s.dead + makes a s f r ≤ s.room
    · simp only [step, if_pos h, Inv]
      simp only [makes, revives, max_def, min_def] at h roomy ⊢
      split_ifs at * <;> omega
    · simp only [step, if_neg h, Inv]
      simp only [makes, revives, max_def, min_def] at h roomy ⊢
      split_ifs at * <;> omega
  | remove k =>
    by_cases h₁ : s.slots < a
    · simp only [step, if_pos h₁]
      exact ⟨held, few, fit, floor, roomy⟩
    · by_cases h₂ : 2 * (s.slots - a) + c₀ < s.dead + kills a s k
      · simp only [step, if_neg h₁, if_pos h₂, Inv]
        simp only [kills, max_def, min_def] at h₂ roomy ⊢
        split_ifs at * <;> omega
      · simp only [step, if_neg h₁, if_neg h₂, Inv]
        simp only [kills, max_def, min_def] at h₂ roomy ⊢
        split_ifs at * <;> omega

theorem run_inv (a c₀ : Nat) (ac : a ≤ c₀) (ops : List Op) :
    ∀ s, Inv c₀ s → Inv c₀ (run a c₀ s ops) := by
  induction ops with
  | nil => intro s inv; exact inv
  | cons op ops ih =>
    intro s inv
    exact ih (step a c₀ s op) (step_inv a c₀ ac s op inv)

theorem start_inv (c₀ : Nat) : Inv c₀ ⟨0, 0, 0, c₀, 0⟩ := by
  unfold Inv
  simp only
  omega

/-- From an empty relation with room `c₀`, the numbers stay within three
times the slots plus `c₀`, and the room within the larger of `c₀` and twice
the numbers. -/
theorem numbers_bound (a c₀ : Nat) (ac : a ≤ c₀) (ops : List Op) :
    let s := run a c₀ ⟨0, 0, 0, c₀, 0⟩ ops
    s.live + s.dead ≤ 3 * s.slots + c₀ ∧ s.room ≤ max c₀ (2 * (s.live + s.dead)) := by
  obtain ⟨held, few, _, _, roomy⟩ := run_inv a c₀ ac ops _ (start_inv c₀)
  exact ⟨by omega, roomy⟩

/-- The potential: three per dead number, and twice the numbers beyond half
the room. -/
def potential (s : St) : Nat := 3 * s.dead + (2 * (s.live + s.dead) - s.room)

/-- Each operation's work, with the potential it leaves, stays within the
potential before plus `3 a`. -/
theorem step_amortized (a c₀ : Nat) (ac : a ≤ c₀) (s : St) (op : Op)
    (inv : Inv c₀ s) :
    (step a c₀ s op).work + potential (step a c₀ s op) ≤
      s.work + potential s + 3 * a := by
  obtain ⟨held, few, fit, floor, roomy⟩ := inv
  cases op with
  | add f r =>
    by_cases h : s.live + s.dead + makes a s f r ≤ s.room
    · simp only [step, if_pos h, potential]
      simp only [makes, revives, max_def, min_def] at h roomy ⊢
      split_ifs at * <;> omega
    · simp only [step, if_neg h, potential]
      simp only [makes, revives, max_def, min_def] at h roomy ⊢
      split_ifs at * <;> omega
  | remove k =>
    by_cases h₁ : s.slots < a
    · simp only [step, if_pos h₁]
      omega
    · by_cases h₂ : 2 * (s.slots - a) + c₀ < s.dead + kills a s k
      · simp only [step, if_neg h₁, if_pos h₂, potential]
        simp only [kills, max_def, min_def] at h₂ roomy ⊢
        split_ifs at * <;> omega
      · simp only [step, if_neg h₁, if_neg h₂, potential]
        simp only [kills, max_def, min_def] at h₂ roomy ⊢
        split_ifs at * <;> omega

/-- From an empty relation with room `c₀`, the work of any run stays within
`3 a` per operation. -/
theorem work_amortized (a c₀ : Nat) (ac : a ≤ c₀) (ops : List Op) :
    (run a c₀ ⟨0, 0, 0, c₀, 0⟩ ops).work ≤ 3 * a * ops.length := by
  suffices h : ∀ s, Inv c₀ s →
      (run a c₀ s ops).work + potential (run a c₀ s ops) ≤
        s.work + potential s + 3 * a * ops.length by
    have hrun := h ⟨0, 0, 0, c₀, 0⟩ (start_inv c₀)
    simp only [potential] at hrun
    omega
  induction ops with
  | nil => intro s _; simp [run]
  | cons op ops ih =>
    intro s inv
    have hstep := step_amortized a c₀ ac s op inv
    have hrest := ih (step a c₀ s op) (step_inv a c₀ ac s op inv)
    simp only [run, List.length_cons, Nat.mul_succ]
    omega

/-- Churn on one fact of two columns, each time over fresh ids: two rounds
leave four dead numbers, which the bound allows; the third round's removal
finds six, past twice the slots plus `c₀`, and rebuilds to none. -/
example :
    (run 2 4 ⟨0, 0, 0, 4, 0⟩ [.add 2 0, .remove 2, .add 2 0, .remove 2]).dead = 4 := by
  decide

example :
    let s := run 2 4 ⟨0, 0, 0, 4, 0⟩
      [.add 2 0, .remove 2, .add 2 0, .remove 2, .add 2 0, .remove 2]
    s.dead = 0 ∧ s.room = 4 := by
  decide

/-- A fact taken out and put back revives its numbers: nothing dies for good
and nothing is rebuilt. -/
example :
    let s := run 2 4 ⟨0, 0, 0, 4, 0⟩ [.add 2 0, .remove 2, .add 0 2]
    s.live = 2 ∧ s.dead = 0 ∧ s.work = 0 := by
  decide

end Mettapedia.Machines.RelationNumberingCost
