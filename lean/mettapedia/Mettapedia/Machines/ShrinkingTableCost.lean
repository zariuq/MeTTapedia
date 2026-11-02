import Mathlib.Tactic

/-!
# A table that shrinks with its contents: room within four times the live

A relation kept as a table grew its room as tuples came and kept it when they
went: 200,000 pairs removed down to 64 left the room of 200,000.  The room
now doubles when full and, once three quarters of it stand empty and it is at
least twice the first room `c₀`, halves on the removal that finds it so.  A
resize copies the live entries.  Rooms are `c₀` times powers of two, so
halving is exact, and a table halved stands half full: the next resize is as
far off as the last one was.

The model: the room `cap`, the live entries `live`, and the copying paid so
far.  A removal from an empty table changes nothing.  This file proves:
* `room_bound`: from an empty table at the first room, the room never
  exceeds the larger of twice the first room and four times the live
  entries;
* `copies_amortized`: the copying of any run stays within four per operation
  plus the first room, by a potential on the room's distance from twice the
  entries.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShrinkingTableCost

structure St where
  cap : Nat
  live : Nat
  copied : Nat

inductive Op
  | add
  | remove

/-- An add doubles a full table, copying its entries; a removal that leaves
three quarters of a room of at least twice the first room empty halves it,
copying the entries left. -/
def step (c₀ : Nat) (s : St) : Op → St
  | .add =>
    if s.live < s.cap then ⟨s.cap, s.live + 1, s.copied⟩
    else ⟨2 * s.cap, s.live + 1, s.copied + s.live⟩
  | .remove =>
    if s.live = 0 then s
    else if 2 * c₀ ≤ s.cap ∧ 4 * (s.live - 1) < s.cap then
      ⟨s.cap / 2, s.live - 1, s.copied + (s.live - 1)⟩
    else ⟨s.cap, s.live - 1, s.copied⟩

def run (c₀ : Nat) (s : St) : List Op → St
  | [] => s
  | op :: ops => run c₀ (step c₀ s op) ops

/-- The invariant: the entries fit, the room is at least the first room, and
it is below twice the first room or within four times the entries. -/
def Inv (c₀ : Nat) (s : St) : Prop :=
  s.live ≤ s.cap ∧ c₀ ≤ s.cap ∧ (s.cap < 2 * c₀ ∨ s.cap ≤ 4 * s.live)

theorem step_inv (c₀ : Nat) (pos : 2 ≤ c₀) (s : St) (op : Op) (inv : Inv c₀ s) :
    Inv c₀ (step c₀ s op) := by
  obtain ⟨fit, floor, small⟩ := inv
  unfold Inv
  cases op with
  | add =>
    simp only [step]
    split <;> simp only <;> omega
  | remove =>
    simp only [step]
    split
    · exact ⟨fit, floor, small⟩
    · split <;> simp only <;> omega

theorem run_inv (c₀ : Nat) (pos : 2 ≤ c₀) (ops : List Op) :
    ∀ s, Inv c₀ s → Inv c₀ (run c₀ s ops) := by
  induction ops with
  | nil => intro s inv; exact inv
  | cons op ops ih =>
    intro s inv
    exact ih (step c₀ s op) (step_inv c₀ pos s op inv)

theorem start_inv (c₀ : Nat) (pos : 2 ≤ c₀) : Inv c₀ ⟨c₀, 0, 0⟩ :=
  ⟨Nat.zero_le _, le_refl _, Or.inl (by show c₀ < 2 * c₀; omega)⟩

/-- From an empty table at the first room, the room never exceeds the larger
of twice the first room and four times the live entries. -/
theorem room_bound (c₀ : Nat) (pos : 2 ≤ c₀) (ops : List Op) :
    (run c₀ ⟨c₀, 0, 0⟩ ops).cap ≤
      max (2 * c₀) (4 * (run c₀ ⟨c₀, 0, 0⟩ ops).live) := by
  obtain ⟨_, _, small⟩ := run_inv c₀ pos ops _ (start_inv c₀ pos)
  rcases small with h₁ | h₁
  · exact le_trans h₁.le (le_max_left _ _)
  · exact le_trans h₁ (le_max_right _ _)

/-- The potential: the room's distance from twice the entries, counted twice
when the room is the smaller. -/
def potential (s : St) : Nat :=
  if s.cap ≤ 2 * s.live then 2 * (2 * s.live - s.cap) else s.cap - 2 * s.live

/-- Each operation's copying, with the potential it leaves, stays within the
potential before plus four. -/
theorem step_amortized (c₀ : Nat) (pos : 2 ≤ c₀) (s : St) (op : Op)
    (inv : Inv c₀ s) :
    (step c₀ s op).copied + potential (step c₀ s op) ≤
      s.copied + potential s + 4 := by
  obtain ⟨fit, floor, small⟩ := inv
  cases op with
  | add =>
    simp only [step]
    split <;> simp only [potential] <;> split <;> split <;> omega
  | remove =>
    simp only [step]
    split
    · omega
    · split <;> simp only [potential] <;> split <;> split <;> omega

/-- From an empty table at the first room, the copying of any run of
operations stays within four per operation plus the first room. -/
theorem copies_amortized (c₀ : Nat) (pos : 2 ≤ c₀) (ops : List Op) :
    (run c₀ ⟨c₀, 0, 0⟩ ops).copied ≤ 4 * ops.length + c₀ := by
  suffices h : ∀ s, Inv c₀ s →
      (run c₀ s ops).copied + potential (run c₀ s ops) ≤
        s.copied + potential s + 4 * ops.length by
    have hrun := h ⟨c₀, 0, 0⟩ (start_inv c₀ pos)
    have hstart : potential ⟨c₀, 0, 0⟩ = c₀ := by
      simp only [potential]
      split <;> omega
    rw [hstart] at hrun
    dsimp only at hrun
    omega
  induction ops with
  | nil => intro s _; simp [run]
  | cons op ops ih =>
    intro s inv
    have hstep := step_amortized c₀ pos s op inv
    have hrest := ih (step c₀ s op) (step_inv c₀ pos s op inv)
    simp only [run, List.length_cons]
    omega

/-- Doubling and halving keep the room `c₀` times a power of two, so halving
is exact. -/
theorem room_power (c₀ : Nat) (ops : List Op) :
    ∀ s : St, (∃ k, s.cap = c₀ * 2 ^ k) →
      ∃ k, (run c₀ s ops).cap = c₀ * 2 ^ k := by
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih =>
    intro s ⟨k, hk⟩
    apply ih
    cases op with
    | add =>
      simp only [step]
      split
      · exact ⟨k, hk⟩
      · exact ⟨k + 1, by rw [hk, pow_succ]; ring⟩
    | remove =>
      simp only [step]
      split
      · exact ⟨k, hk⟩
      · split
        · rename_i h
          cases k with
          | zero =>
            refine ⟨0, ?_⟩
            dsimp only
            simp only [pow_zero, mul_one] at hk ⊢
            omega
          | succ k =>
            refine ⟨k, ?_⟩
            dsimp only
            rw [hk, pow_succ, ← mul_assoc, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
        · exact ⟨k, hk⟩

/-- A run that keeps a table full one entry past a doubling, then removes
down to a quarter, pays one doubling and one halving: a positive example of
the bound at work. -/
example : (run 4 ⟨4, 0, 0⟩
    [.add, .add, .add, .add, .add, .remove, .remove, .remove, .remove]).cap = 4 := by
  decide

/-- Without the halving the room would stay at its high-water mark: the same
run with removals that never reach a quarter keeps the doubled room. -/
example : (run 4 ⟨4, 0, 0⟩ [.add, .add, .add, .add, .add, .remove, .remove]).cap = 8 := by
  decide

end Mettapedia.Machines.ShrinkingTableCost
