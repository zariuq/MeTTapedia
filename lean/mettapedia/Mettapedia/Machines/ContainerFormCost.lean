import Mathlib.Tactic

/-!
# A chunk of a row: an array while it is small, bits while it is full

A binary relation kept as bits holds, for each first-column number, the
second-column numbers paired with it.  Choosing between a sorted array and
bits by the bytes each would take up to the row's largest number can
oscillate: one huge number put and taken flips the form, at the cost of the
whole row, every few operations.  Split into chunks of the number space, each
chunk's form depends only on its own count: it becomes bits once it holds
more than `hi` numbers and an array again once it holds fewer than `lo`, with
`2 * lo ≤ hi + 1`.  A conversion copies the chunk's numbers.

The model: a chunk's count, its form, and the copying paid.  This file
proves:
* `bits_full`: a chunk kept as bits holds at least `lo` numbers, so its fixed
  room is within `room / lo` per number;
* `array_small`: a chunk kept as an array holds at most `hi` numbers;
* `copies_amortized`: the copying of any run stays within two per operation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ContainerFormCost

inductive Form
  | array
  | bits
  deriving DecidableEq

structure St where
  count : Nat
  form : Form
  copied : Nat

inductive Op
  | put
  | take

/-- A put past `hi` turns an array to bits; a take below `lo` turns bits to an
array; either copies the chunk's numbers.  A take from an empty chunk changes
nothing. -/
def step (lo hi : Nat) (s : St) : Op → St
  | .put =>
    if s.form = .array ∧ hi < s.count + 1 then
      ⟨s.count + 1, .bits, s.copied + (s.count + 1)⟩
    else ⟨s.count + 1, s.form, s.copied⟩
  | .take =>
    if s.count = 0 then s
    else if s.form = .bits ∧ s.count - 1 < lo then
      ⟨s.count - 1, .array, s.copied + (s.count - 1)⟩
    else ⟨s.count - 1, s.form, s.copied⟩

def run (lo hi : Nat) (s : St) : List Op → St
  | [] => s
  | op :: ops => run lo hi (step lo hi s op) ops

/-- The invariant: bits hold at least `lo`, an array at most `hi`. -/
def Inv (lo hi : Nat) (s : St) : Prop :=
  (s.form = .bits → lo ≤ s.count) ∧ (s.form = .array → s.count ≤ hi)

theorem step_inv (lo hi : Nat) (gap : 2 * lo ≤ hi + 1) (s : St) (op : Op)
    (inv : Inv lo hi s) : Inv lo hi (step lo hi s op) := by
  obtain ⟨n, f, c⟩ := s
  obtain ⟨hb, ha⟩ := inv
  cases f <;> cases op <;> simp only [Inv, step] at hb ha ⊢ <;> split_ifs <;>
    simp_all <;> omega

theorem run_inv (lo hi : Nat) (gap : 2 * lo ≤ hi + 1) (ops : List Op) :
    ∀ s, Inv lo hi s → Inv lo hi (run lo hi s ops) := by
  induction ops with
  | nil => intro s inv; exact inv
  | cons op ops ih =>
    intro s inv
    exact ih (step lo hi s op) (step_inv lo hi gap s op inv)

/-- A chunk kept as bits holds at least `lo` numbers. -/
theorem bits_full (lo hi : Nat) (gap : 2 * lo ≤ hi + 1) (ops : List Op) :
    (run lo hi ⟨0, .array, 0⟩ ops).form = .bits →
      lo ≤ (run lo hi ⟨0, .array, 0⟩ ops).count :=
  (run_inv lo hi gap ops _ ⟨fun h => absurd h (by simp), fun _ => Nat.zero_le _⟩).1

/-- A chunk kept as an array holds at most `hi` numbers. -/
theorem array_small (lo hi : Nat) (gap : 2 * lo ≤ hi + 1) (ops : List Op) :
    (run lo hi ⟨0, .array, 0⟩ ops).form = .array →
      (run lo hi ⟨0, .array, 0⟩ ops).count ≤ hi :=
  (run_inv lo hi gap ops _ ⟨fun h => absurd h (by simp), fun _ => Nat.zero_le _⟩).2

/-- The potential: twice the distance the count has come since the chunk's
last conversion, measured from the threshold it would cross back. -/
def potential (lo hi : Nat) (s : St) : Nat :=
  match s.form with
  | .array => 2 * (s.count - (lo - 1))
  | .bits => 2 * ((hi + 1) - s.count)

theorem step_amortized (lo hi : Nat) (gap : 2 * lo ≤ hi + 1) (pos : 1 ≤ lo)
    (s : St) (op : Op) (inv : Inv lo hi s) :
    (step lo hi s op).copied + potential lo hi (step lo hi s op) ≤
      s.copied + potential lo hi s + 2 := by
  obtain ⟨n, f, c⟩ := s
  obtain ⟨hb, ha⟩ := inv
  cases f <;> cases op <;> simp only [step, potential] at hb ha ⊢ <;>
    split_ifs <;> simp_all <;> omega

/-- From an empty chunk, the copying of any run of operations stays within
two per operation. -/
theorem copies_amortized (lo hi : Nat) (gap : 2 * lo ≤ hi + 1) (pos : 1 ≤ lo)
    (ops : List Op) : (run lo hi ⟨0, .array, 0⟩ ops).copied ≤ 2 * ops.length := by
  suffices h : ∀ s, Inv lo hi s →
      (run lo hi s ops).copied + potential lo hi (run lo hi s ops) ≤
        s.copied + potential lo hi s + 2 * ops.length by
    have hrun := h ⟨0, .array, 0⟩ ⟨fun h => absurd h (by simp), fun _ => Nat.zero_le _⟩
    have hstart : potential lo hi ⟨0, .array, 0⟩ = 0 := by
      simp only [potential]
      omega
    rw [hstart] at hrun
    dsimp only at hrun
    omega
  induction ops with
  | nil => intro s _; simp [run]
  | cons op ops ih =>
    intro s inv
    have hstep := step_amortized lo hi gap pos s op inv
    have hrest := ih (step lo hi s op) (step_inv lo hi gap s op inv)
    simp only [run, List.length_cons]
    omega

/-- A chunk filled past `hi` turns to bits once; one number in and out at the
threshold flips it no more. -/
example :
    let s := run 2 4 ⟨0, .array, 0⟩ [.put, .put, .put, .put, .put, .take, .put, .take]
    s.form = .bits ∧ s.copied = 5 := by
  decide

/-- Emptied below `lo`, it is an array again. -/
example :
    (run 2 4 ⟨0, .array, 0⟩ [.put, .put, .put, .put, .put, .take, .take, .take, .take]).form
      = .array := by
  decide

end Mettapedia.Machines.ContainerFormCost
