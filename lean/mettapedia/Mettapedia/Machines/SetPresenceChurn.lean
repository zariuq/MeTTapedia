import Mathlib.Tactic

/-!
# A set's presence index under churn: rebuilt after each removal, or updated

A set space answers "does a row with this alpha key exist?" from a presence
index: the set of the rows' keys.  Adding a row adds its key.  A removal used
to mark the index stale, and the next membership check rebuilt it from every
row, so a churn of `m` removals each followed by an add, over `n` rows, cost
`m * n` key computations.  While no two rows share a key, which the rebuild
and the additions observe as they set each row's key, a removal can take its
row's key out of the index directly: one key computation.  Once two rows share
a key, a removal marks the index stale as before.

The model keeps the rows' keys as a list and the index as a finite set.  This
file proves:
* `exact_add`, `exact_remove`: adding and, for rows with distinct keys,
  removing keep the index equal to the rows' keys;
* `bag_remove_inexact`: without distinct keys, taking the removed row's key out
  of the index loses a key another row still has;
* `churn_rebuild_cost`, `churn_update_cost`: the churn family costs `m * n`
  rebuilt keys against `2 * m` computed keys;
* `compaction_amortized`: the list of held keys, compacted when it passes
  twice the rows plus a margin, costs at most twice the keys added.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SetPresenceChurn

variable {Key : Type} [DecidableEq Key]

/-- Adding a row with a new key: the index takes the key. -/
theorem exact_add (rows : List Key) (index : Finset Key)
    (exact : index = rows.toFinset) (k : Key) :
    insert k index = (rows ++ [k]).toFinset := by
  rw [exact, List.toFinset_append]
  ext x
  simp

/-- Removing a row of a set (keys distinct): the index loses its key and
stays the rows' keys. -/
theorem exact_remove (rows : List Key) (index : Finset Key)
    (exact : index = rows.toFinset) (distinct : rows.Nodup) (k : Key) :
    index.erase k = (rows.erase k).toFinset := by
  rw [exact]
  ext x
  simp only [Finset.mem_erase, List.mem_toFinset]
  constructor
  · rintro ⟨hne, hx⟩
    exact (List.mem_erase_of_ne hne).mpr hx
  · intro hx
    refine ⟨?_, List.mem_of_mem_erase hx⟩
    rintro rfl
    exact (List.Nodup.not_mem_erase distinct) hx

/-- A bag may hold one key in two rows: taking the removed row's key out of
the index loses the key the other row still has. -/
theorem bag_remove_inexact (k : Key) :
    ([k, k] : List Key).toFinset.erase k ≠ (([k, k] : List Key).erase k).toFinset := by
  simp

/-- The churn family under rebuilding: `m` rounds, each a removal and an add
over `n` rows, the add's membership check rebuilding every row's key. -/
def churnRebuild (n m : Nat) : Nat := m * n

/-- The same churn updating the index: one key computed by the removal and
one by the add. -/
def churnUpdate (m : Nat) : Nat := 2 * m

/-- One round of rebuilding: the membership check after a removal computes
the key of each of the `n` rows. -/
def rebuildRound (n : Nat) : Nat := (List.range n).length

theorem churn_rebuild_cost (n m : Nat) :
    ((List.range m).map (fun _ => rebuildRound n)).sum = churnRebuild n m := by
  simp [rebuildRound, churnRebuild, List.sum_replicate, Nat.mul_comm]

theorem churn_update_cost (m : Nat) :
    ((List.range m).map (fun _ => 2)).sum = churnUpdate m := by
  simp [churnUpdate, List.sum_replicate, Nat.mul_comm]

/-! ## Compacting the held keys

A key that is no row's id is held by the index while a row has it.  A removal
leaves its key in the held list; when the list passes twice the rows plus a
margin `c`, a compaction walks it, keeping only the keys rows still have.  The
state: the list's length `len` and the rows `rows`; an add appends one key and
one row, a removal takes one row; a compaction costs `len` and leaves at most
`rows` keys. -/

/-- One operation: an add (a key and a row) or a removal (a row). -/
inductive Op
  | add
  | remove

structure St where
  len : Nat
  rows : Nat
  cost : Nat

/-- An operation, then a compaction if the list passed `2 * rows + c`. -/
def step (c : Nat) (s : St) : Op → St
  | .add =>
    let s' : St := ⟨s.len + 1, s.rows + 1, s.cost⟩
    if 2 * s'.rows + c < s'.len then ⟨s'.rows, s'.rows, s'.cost + s'.len⟩ else s'
  | .remove =>
    let s' : St := ⟨s.len, s.rows - 1, s.cost⟩
    if 2 * s'.rows + c < s'.len then ⟨s'.rows, s'.rows, s'.cost + s'.len⟩ else s'

def run (c : Nat) (s : St) : List Op → St
  | [] => s
  | op :: ops => run c (step c s op) ops

def adds : List Op → Nat
  | [] => 0
  | .add :: ops => adds ops + 1
  | .remove :: ops => adds ops

/-- The potential: twice the list's length less the rows it may keep. -/
def potential (s : St) : Nat := 2 * s.len

/-- Each operation's cost, plus the potential it leaves, stays within the
potential before plus two for an add: compaction is paid by the keys it
drops. -/
theorem step_amortized (c : Nat) (s : St) (op : Op) (inv : s.rows ≤ s.len) :
    (step c s op).cost + potential (step c s op) ≤
      s.cost + potential s + (match op with | .add => 2 | .remove => 0) ∧
      (step c s op).rows ≤ (step c s op).len := by
  cases op with
  | add =>
    simp only [step, potential]
    split
    · constructor <;> simp; omega
    · constructor <;> simp <;> omega
  | remove =>
    simp only [step, potential]
    split
    · constructor <;> simp; omega
    · constructor <;> simp; omega

/-- Over any sequence of operations from an empty list, compaction costs at
most twice the keys added. -/
theorem compaction_amortized (c : Nat) (ops : List Op) :
    (run c ⟨0, 0, 0⟩ ops).cost ≤ 2 * adds ops := by
  suffices h : ∀ (s : St), s.rows ≤ s.len →
      (run c s ops).cost + potential (run c s ops) ≤
        s.cost + potential s + 2 * adds ops by
    have := h ⟨0, 0, 0⟩ (le_refl 0)
    simp only [potential] at this
    omega
  induction ops with
  | nil => intro s _; simp [run, adds]
  | cons op ops ih =>
    intro s inv
    obtain ⟨hstep, hinv⟩ := step_amortized c s op inv
    have hrun := ih (step c s op) hinv
    cases op with
    | add =>
      dsimp only at hstep
      simp only [run, adds] at hrun ⊢
      omega
    | remove =>
      dsimp only at hstep
      simp only [run, adds] at hrun ⊢
      omega

end Mettapedia.Machines.SetPresenceChurn
