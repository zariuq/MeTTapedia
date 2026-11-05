import Mathlib.Tactic

/-!
# Shared prepends: flat buffers with front slack against chunked lists

CeTTa builds complete lists flat: an expression whose children are the top of a
buffer with a free slot below them takes a prepend in place, by claiming that slot.
That makes a prepend O(1) while one holder prepends.  When a second holder prepends
onto the same list, the slot is taken and the list is copied.

Measured (11/04, frozen opt binary): a loop that keeps its accumulator and also
prepends onto it a second time,
`(build3 (- $n 1) (cons $n $acc) (cons 0 $acc))`, costs 17.7M / 65.9M / 256.7M /
1364.6M instructions at n = 2k / 4k / 8k / 16k, against 7.2M / 10.7M / 17.6M / 36.1M
when the second prepend goes onto another list: 38x at 16k and growing with n.

The model: a flat list value is its elements and whether the slot below its first
element is free.  A prepend onto a value whose slot is free claims it (cost 1) and
leaves the old holder with a claimed slot; a prepend onto a value whose slot is taken
copies it (cost: its length plus one).  A chunked list (a cons cell, or a VList chunk)
prepends by pointing at the shared tail (cost 1).

This file proves:
* `Flat.prepend_elems`, `Flat.prepend_old_elems`: a prepend answers `x :: l` and the
  old holder still reads `l`, on both paths, so the representations agree on every
  observation (exact transfer);
* `uniqueFlat_total`: one prepend per step costs `n` on the flat form;
* `sharedFlat_total`: two prepends per step onto the same accumulator cost
  `n * (n + 3) / 2` on the flat form, while `sharedChunked_total` is `2 * n`;
* `sharedFlat_exceeds`: past `n = 4 c`, the flat form pays more than `c` times the
  chunked form, for every `c`: no constant factor covers the cliff.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedPrependCost

/-- A flat list value: its elements, and whether the slot below its first element is
free. -/
structure Flat where
  elems : List ℕ
  frontFree : Bool

/-- Prepend `x` onto `l`: the new value, the old value as its holder now sees it, and
the cost.  A free slot is claimed in place; a taken slot forces a copy, into a buffer
that again has a free slot below its first element. -/
def Flat.prepend (x : ℕ) (l : Flat) : Flat × Flat × ℕ :=
  if l.frontFree then (⟨x :: l.elems, true⟩, ⟨l.elems, false⟩, 1)
  else (⟨x :: l.elems, true⟩, l, l.elems.length + 1)

theorem Flat.prepend_elems (x : ℕ) (l : Flat) : (l.prepend x).1.elems = x :: l.elems := by
  unfold Flat.prepend; split <;> rfl

theorem Flat.prepend_old_elems (x : ℕ) (l : Flat) : (l.prepend x).2.1.elems = l.elems := by
  unfold Flat.prepend; split <;> rfl

theorem Flat.prepend_frontFree (x : ℕ) (l : Flat) : (l.prepend x).1.frontFree = true := by
  unfold Flat.prepend; split <;> rfl

/-- A claim leaves the old holder's slot taken. -/
theorem Flat.prepend_claims (x : ℕ) (l : Flat) (h : l.frontFree = true) :
    (l.prepend x).2.1.frontFree = false ∧ (l.prepend x).2.2 = 1 := by
  simp [Flat.prepend, h]

/-- A prepend onto a taken slot copies the list. -/
theorem Flat.prepend_copies (x : ℕ) (l : Flat) (h : l.frontFree = false) :
    (l.prepend x).2.2 = l.elems.length + 1 := by
  simp [Flat.prepend, h]

/-- One prepend per step, onto the accumulator: the state after `k` steps and the
cost so far. -/
def uniqueFlat : ℕ → Flat × ℕ
  | 0 => (⟨[], true⟩, 0)
  | k + 1 =>
    let (acc, c) := uniqueFlat k
    let (next, _, step) := acc.prepend k
    (next, c + step)

theorem uniqueFlat_state (k : ℕ) :
    (uniqueFlat k).1.frontFree = true ∧ (uniqueFlat k).1.elems.length = k := by
  induction k with
  | zero => simp [uniqueFlat]
  | succ k ih =>
    simp only [uniqueFlat]
    refine ⟨Flat.prepend_frontFree _ _, ?_⟩
    rw [Flat.prepend_elems, List.length_cons, ih.2]

theorem uniqueFlat_total (n : ℕ) : (uniqueFlat n).2 = n := by
  induction n with
  | zero => simp [uniqueFlat]
  | succ k ih =>
    simp only [uniqueFlat]
    rw [(Flat.prepend_claims k _ (uniqueFlat_state k).1).2, ih]

/-- Two prepends per step onto the same accumulator: the accumulator continues with
the first, and the second is kept by another holder (as `(cons 0 $acc)` is). -/
def sharedFlat : ℕ → Flat × ℕ
  | 0 => (⟨[], true⟩, 0)
  | k + 1 =>
    let (acc, c) := sharedFlat k
    let (next, held, first) := acc.prepend k
    let (_, _, second) := held.prepend 0
    (next, c + first + second)

theorem sharedFlat_state (k : ℕ) :
    (sharedFlat k).1.frontFree = true ∧ (sharedFlat k).1.elems.length = k := by
  induction k with
  | zero => simp [sharedFlat]
  | succ k ih =>
    simp only [sharedFlat]
    refine ⟨Flat.prepend_frontFree _ _, ?_⟩
    rw [Flat.prepend_elems, List.length_cons, ih.2]

/-- Step `k` pays one for the claim and `k + 1` for the copy. -/
theorem sharedFlat_step (k : ℕ) : (sharedFlat (k + 1)).2 = (sharedFlat k).2 + (k + 2) := by
  simp only [sharedFlat]
  have hs := sharedFlat_state k
  have hclaim := Flat.prepend_claims k _ hs.1
  rw [hclaim.2, Flat.prepend_copies 0 _ hclaim.1, Flat.prepend_old_elems, hs.2]
  ring

theorem sharedFlat_total (n : ℕ) : 2 * (sharedFlat n).2 = n * (n + 3) := by
  induction n with
  | zero => simp [sharedFlat]
  | succ k ih =>
    rw [sharedFlat_step, mul_add, ih]
    ring

/-- A chunked list prepends by pointing at the shared tail: every prepend costs one. -/
def chunkedPrepend (x : ℕ) (l : List ℕ) : List ℕ × ℕ := (x :: l, 1)

def sharedChunked : ℕ → List ℕ × ℕ
  | 0 => ([], 0)
  | k + 1 =>
    let (acc, c) := sharedChunked k
    let (next, first) := chunkedPrepend k acc
    let (_, second) := chunkedPrepend 0 acc
    (next, c + first + second)

theorem sharedChunked_total (n : ℕ) : (sharedChunked n).2 = 2 * n := by
  induction n with
  | zero => simp [sharedChunked]
  | succ k ih =>
    simp only [sharedChunked, chunkedPrepend]
    rw [ih]; ring

/-- Both forms carry the same accumulator: exact transfer of the observed lists. -/
theorem shared_same_lists (n : ℕ) : (sharedFlat n).1.elems = (sharedChunked n).1 := by
  induction n with
  | zero => simp [sharedFlat, sharedChunked]
  | succ k ih =>
    simp only [sharedFlat, sharedChunked, chunkedPrepend]
    rw [Flat.prepend_elems, ih]

/-- No constant factor covers the cliff: past `n = 4 c`, the flat form pays more than
`c` times the chunked form. -/
theorem sharedFlat_exceeds (c n : ℕ) (hn : 4 * c < n) :
    c * (sharedChunked n).2 < (sharedFlat n).2 := by
  have h2 := sharedFlat_total n
  rw [sharedChunked_total]
  have hpos : 0 < n := by omega
  nlinarith

end Mettapedia.Machines.SharedPrependCost
