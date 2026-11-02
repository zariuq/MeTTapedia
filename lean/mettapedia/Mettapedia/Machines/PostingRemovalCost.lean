import Mathlib.Tactic

/-!
# Removing rows from a column index: shifting each time, or marking and settling

A column index keeps, for each key, the rows holding it as a sorted posting.
Removing a row eagerly finds it and shifts every later entry down one slot,
so removing a posting's rows in ascending order shifts `n * (n - 1) / 2`
entries in all.

A space that marks removed rows can leave its postings alone: a reader that
meets a marked row drops it, and when the marks reach half the rows they are
settled, one pass over the posting dropping every marked row.  A removal then
costs one step, a settle costs the posting's length, and since a settle comes
only once the marks reach half that length, the settles cost at most two steps
per removal: at most three per removal in all.

This file proves:
* `eager_ascending_cost`: removing `0, …, n - 1` from `[0, …, n - 1]` in
  ascending order shifts `n * (n - 1) / 2` entries (twice that is
  `n * (n - 1)`);
* `lazy_cost_le`: marking and settling at half costs at most `3` per removal,
  for any sequence of removals of distinct rows the posting holds;
* `lazy_reads_eager`: the posting read through its marks is the one eager
  removal leaves.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PostingRemovalCost

/-! ## Eager removal -/

/-- Removing `x` eagerly: the posting without it, and the entries after it that
shift down one slot. -/
def eagerRemove (l : List Nat) (x : Nat) : List Nat × Nat :=
  (l.erase x, l.length - l.idxOf x - 1)

/-- Removing each of `xs` in turn, summing the shifts. -/
def eagerAll (l : List Nat) : List Nat → List Nat × Nat
  | [] => (l, 0)
  | x :: xs =>
    let r := eagerRemove l x
    let rest := eagerAll r.1 xs
    (rest.1, r.2 + rest.2)

theorem eagerAll_range' (i n : Nat) :
    (eagerAll (List.range' i n) (List.range' i n)).1 = [] ∧
      2 * (eagerAll (List.range' i n) (List.range' i n)).2 = n * (n - 1) := by
  induction n generalizing i with
  | zero => simp [eagerAll]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (i + 1)
    rw [List.range'_succ, eagerAll]
    simp only [eagerRemove, List.erase_cons_head, List.idxOf_cons_self,
      List.length_cons, List.length_range']
    refine ⟨h1, ?_⟩
    generalize (eagerAll (List.range' (i + 1) n) (List.range' (i + 1) n)).2 = c at h2 ⊢
    have e : n + 1 - 0 - 1 = n := by omega
    rw [e]
    rcases n with _ | n
    · simp at h2 ⊢; omega
    · simp only [Nat.add_sub_cancel] at h2 ⊢
      nlinarith [h2]

theorem eager_ascending_cost (n : Nat) :
    2 * (eagerAll (List.range n) (List.range n)).2 = n * (n - 1) := by
  rw [List.range_eq_range']
  exact (eagerAll_range' 0 n).2

/-! ## Marking, and settling at half -/

/-- A posting with its marked rows. -/
structure Lazy where
  rows : List Nat
  marks : Finset Nat

/-- What a reader sees: the rows not marked. -/
def Lazy.read (s : Lazy) : List Nat := s.rows.filter (· ∉ s.marks)

/-- Marking `x`: one step; then, once the marks reach half the posting, a
settle drops every marked row, at the cost of one pass. -/
def lazyRemove (s : Lazy) (x : Nat) : Lazy × Nat :=
  if s.rows.length ≤ 2 * (insert x s.marks).card then
    (⟨s.rows.filter (· ∉ insert x s.marks), ∅⟩, 1 + s.rows.length)
  else
    (⟨s.rows, insert x s.marks⟩, 1)

/-- Marking each of `xs` in turn, summing the steps. -/
def lazyAll (s : Lazy) : List Nat → Lazy × Nat
  | [] => (s, 0)
  | x :: xs =>
    let r := lazyRemove s x
    let rest := lazyAll r.1 xs
    (rest.1, r.2 + rest.2)

/-- The rows a removal may name: held, and not marked yet. -/
def Removable (s : Lazy) (x : Nat) : Prop := x ∈ s.rows ∧ x ∉ s.marks

/-- The marks name only rows the posting holds. -/
def Sound (s : Lazy) : Prop := s.marks ⊆ s.rows.toFinset

theorem lazyRemove_sound (s : Lazy) (x : Nat) (hs : Sound s) (hx : Removable s x) :
    Sound (lazyRemove s x).1 := by
  unfold lazyRemove
  split
  · intro y hy; simp at hy
  · intro y hy
    simp only [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact List.mem_toFinset.mpr hx.1
    · exact hs hy

/-- Amortized: the steps so far plus two per standing mark stay within three per
removal. -/
theorem lazyAll_cost (xs : List Nat) :
    ∀ s : Lazy, Sound s → xs.Nodup → (∀ x ∈ xs, Removable s x) →
      (lazyAll s xs).2 + 2 * (lazyAll s xs).1.marks.card ≤
        2 * s.marks.card + 3 * xs.length := by
  induction xs with
  | nil => intro s _ _ _; simp [lazyAll]
  | cons x xs ih =>
    intro s hs hnd hrem
    obtain ⟨hx, hxs⟩ := List.nodup_cons.mp hnd
    have hrx := hrem x (List.mem_cons_self ..)
    -- After the first removal the rest are still removable.
    have hrest : ∀ y ∈ xs, Removable (lazyRemove s x).1 y := by
      intro y hy
      have hry := hrem y (List.mem_cons_of_mem _ hy)
      have hyx : y ≠ x := fun h => hx (h ▸ hy)
      unfold lazyRemove
      split
      · refine ⟨?_, by simp⟩
        simp only [List.mem_filter, Finset.mem_insert, hyx, hry.2,
          or_false, not_false_eq_true, decide_true, and_true]
        exact hry.1
      · exact ⟨hry.1, by simp [hyx, hry.2]⟩
    have hsound := lazyRemove_sound s x hs hrx
    have := ih (lazyRemove s x).1 hsound hxs hrest
    simp only [lazyAll, List.length_cons]
    have hcard : (insert x s.marks).card = s.marks.card + 1 :=
      Finset.card_insert_of_notMem hrx.2
    by_cases hc : s.rows.length ≤ 2 * (insert x s.marks).card
    · simp only [lazyRemove, if_pos hc, Finset.card_empty, mul_zero, zero_add] at this ⊢
      rw [hcard] at hc
      omega
    · simp only [lazyRemove, if_neg hc] at this ⊢
      rw [hcard] at this
      omega

/-- From a posting with no marks, `k` removals cost at most `3 * k`. -/
theorem lazy_cost_le (rows xs : List Nat) (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ rows) :
    (lazyAll ⟨rows, ∅⟩ xs).2 ≤ 3 * xs.length := by
  have h := lazyAll_cost xs ⟨rows, ∅⟩ (by intro y hy; simp at hy) hnd
    (fun x hx => ⟨hsub x hx, by simp⟩)
  simp only [Finset.card_empty, mul_zero, zero_add] at h
  omega

/-! ## What the reader sees -/

/-- Marking or settling, the reader sees the posting without the removed rows. -/
theorem lazyRemove_read (s : Lazy) (x : Nat) :
    (lazyRemove s x).1.read = s.read.filter (· ≠ x) := by
  unfold lazyRemove Lazy.read
  split
  · simp only [List.filter_filter]
    congr 1; funext y; simp only [Finset.mem_insert, Finset.notMem_empty]
    by_cases hy : y = x <;> simp [hy]
  · simp only [List.filter_filter]
    congr 1; funext y; simp only [Finset.mem_insert]
    by_cases hy : y = x <;> simp [hy]

theorem eagerRemove_nodup (l : List Nat) (x : Nat) (h : l.Nodup) :
    (eagerRemove l x).1 = l.filter (· ≠ x) := by
  simp only [eagerRemove]
  rw [h.erase_eq_filter]
  congr 1; funext y
  by_cases hyx : y = x <;> simp [hyx]

/-- The posting read through its marks is the one eager removal leaves. -/
theorem lazy_reads_eager (xs : List Nat) :
    ∀ (s : Lazy) (l : List Nat), l.Nodup → s.read = l →
      (lazyAll s xs).1.read = (eagerAll l xs).1 := by
  induction xs with
  | nil => intro s l _ h; simpa [lazyAll, eagerAll] using h
  | cons x xs ih =>
    intro s l hnd h
    simp only [lazyAll, eagerAll]
    apply ih
    · rw [eagerRemove_nodup l x hnd]; exact hnd.filter _
    · rw [lazyRemove_read, h, eagerRemove_nodup l x hnd]

end Mettapedia.Machines.PostingRemovalCost
