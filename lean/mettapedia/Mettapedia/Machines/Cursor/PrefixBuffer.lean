import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

/-!
# Prefix buffers: `cons` onto a flat list in amortized constant time

A flat list is a view of a buffer: `len` written slots from `start`.  Buffers
are allocated with free slots below the list, and each buffer records its
front, the lowest slot a view of it starts at.  Prepending an element onto a
view either claims the free slot just below it, when the view starts at its
buffer's front, or copies the list into a fresh buffer that keeps as many free
slots below the copy as the copy is long.

A claim writes one slot below the front and lowers the front.  No view starts
below the front, so no existing view reads a claimed slot, and a claimed slot
is never written again.  Every view therefore reads the same list before and
after any prepend, on every search branch that holds it (`read_stable`).

Along one chain of prepends, each onto the view the last one returned, the
cost is at most three writes per element plus the chain's initial potential
(`run_cost`): claims cost one write, and a copy is paid for by the claims
since the previous copy.  The credit is not shared between branches: a second
branch prepending onto a view that another branch has already extended finds
the front moved and copies (`second_branch_copies`).  Overwriting the claimed
slot instead would change the first branch's list (`reclaim_breaks_first`).

The model is sequential.  A native realization publishes the lowered front
with one atomic compare-and-exchange, so that two threads cannot claim the
same slot; this file states the sequential protocol that exchange realizes.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.PrefixBuffer

variable {α : Type}

/-- A buffer: its written slots, and its front. -/
structure Buffer (α : Type) where
  cell : ℕ → Option α
  front : ℕ

/-- Buffers by address, and the next unused address. -/
structure Heap (α : Type) where
  buf : ℕ → Buffer α
  next : ℕ

/-- A flat list: `len` slots of the buffer at `addr`, from `start`. -/
structure View where
  addr : ℕ
  start : ℕ
  len : ℕ
  deriving DecidableEq, Repr

/-- The list read from `n` slots of a buffer, from slot `s`. -/
def readFrom (b : Buffer α) : ℕ → ℕ → Option (List α)
  | _, 0 => some []
  | s, n + 1 => match b.cell s, readFrom b (s + 1) n with
    | some x, some xs => some (x :: xs)
    | _, _ => none

/-- The list a view reads. -/
def read (H : Heap α) (v : View) : Option (List α) :=
  readFrom (H.buf v.addr) v.start v.len

/-- A view that may still be read: its buffer is allocated, and it starts at
or above the buffer's front. -/
def Live (H : Heap α) (v : View) : Prop :=
  v.addr < H.next ∧ (H.buf v.addr).front ≤ v.start

/-- Reading depends only on the slots read. -/
theorem readFrom_congr {b c : Buffer α} :
    ∀ (s n : ℕ), (∀ i, s ≤ i → i < s + n → b.cell i = c.cell i) →
      readFrom b s n = readFrom c s n
  | _, 0, _ => rfl
  | s, n + 1, h => by
    have hs : b.cell s = c.cell s := h s le_rfl (by omega)
    have hr : readFrom b (s + 1) n = readFrom c (s + 1) n :=
      readFrom_congr (s + 1) n fun i h1 h2 => h i (by omega) (by omega)
    simp only [readFrom, hs, hr]

theorem readFrom_succ {b : Buffer α} {s n : ℕ} {x : α} {xs : List α}
    (hx : b.cell s = some x) (hxs : readFrom b (s + 1) n = some xs) :
    readFrom b s (n + 1) = some (x :: xs) := by
  simp only [readFrom, hx, hxs]

/-! ## Claiming and copying -/

/-- Claim the slot below the front for `x`, lowering the front. -/
def claimBuffer (b : Buffer α) (x : α) : Buffer α where
  cell := Function.update b.cell (b.front - 1) (some x)
  front := b.front - 1

/-- A fresh buffer holding `xs` from slot `slack`, with the slots below it
free. -/
def fresh (xs : List α) (slack : ℕ) : Buffer α where
  cell i := if slack ≤ i then xs[i - slack]? else none
  front := slack

/-- A prepend may claim when the view starts at its buffer's front and a free
slot lies below it. -/
def Claimable (H : Heap α) (v : View) : Prop :=
  0 < v.start ∧ (H.buf v.addr).front = v.start

instance (H : Heap α) (v : View) : Decidable (Claimable H v) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Prepend `x` onto the view `v`, which reads `xs`: the new heap, the new
view, and the slots written. -/
def prepend (H : Heap α) (v : View) (xs : List α) (x : α) :
    Heap α × View × ℕ :=
  if Claimable H v then
    ({ H with buf := Function.update H.buf v.addr (claimBuffer (H.buf v.addr) x) },
     ⟨v.addr, v.start - 1, v.len + 1⟩, 1)
  else
    ({ buf := Function.update H.buf H.next (fresh (x :: xs) (v.len + 1)),
       next := H.next + 1 },
     ⟨H.next, v.len + 1, v.len + 1⟩, v.len + 1)

theorem readFrom_fresh (xs : List α) (slack : ℕ) :
    ∀ (k : ℕ), k ≤ xs.length →
      readFrom (fresh xs slack) (slack + (xs.length - k)) k =
        some (xs.drop (xs.length - k))
  | 0, _ => by simp [readFrom]
  | k + 1, hk => by
    have hlt : xs.length - (k + 1) < xs.length := by omega
    have hcell : (fresh xs slack).cell (slack + (xs.length - (k + 1))) =
        some (xs[xs.length - (k + 1)]) := by
      show (if slack ≤ slack + (xs.length - (k + 1))
          then xs[slack + (xs.length - (k + 1)) - slack]? else none) = _
      rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
        List.getElem?_eq_getElem hlt]
    have hrest := readFrom_fresh xs slack k (by omega)
    have hidx : slack + (xs.length - (k + 1)) + 1 = slack + (xs.length - k) := by
      omega
    rw [readFrom_succ hcell (by rw [hidx]; exact hrest)]
    congr 1
    rw [List.drop_eq_getElem_cons hlt]
    congr 2
    omega

theorem read_fresh (xs : List α) (slack : ℕ) :
    readFrom (fresh xs slack) slack xs.length = some xs := by
  simpa using readFrom_fresh xs slack xs.length le_rfl

/-! ## A prepend reads the extended list and changes no other list -/

theorem read_prepend {H : Heap α} {v : View} {xs : List α} (x : α)
    (hread : read H v = some xs) :
    read (prepend H v xs x).1 (prepend H v xs x).2.1 = some (x :: xs) := by
  unfold prepend
  split
  · next hc =>
    obtain ⟨hpos, hfront⟩ := hc
    simp only [read, Function.update_self]
    have hcell : (claimBuffer (H.buf v.addr) x).cell (v.start - 1) = some x := by
      simp [claimBuffer, hfront]
    have hrest : readFrom (claimBuffer (H.buf v.addr) x) (v.start - 1 + 1) v.len =
        some xs := by
      rw [show v.start - 1 + 1 = v.start by omega, ← hread, read]
      refine readFrom_congr _ _ fun i h1 _ => ?_
      simp only [claimBuffer, hfront]
      rw [Function.update_of_ne (by omega)]
    exact readFrom_succ hcell hrest
  · simp only [read, Function.update_self]
    have hlen : v.len + 1 = (x :: xs).length := by
      have := readFrom_length (H.buf v.addr) v.start v.len xs hread
      simp [this]
    rw [hlen]
    exact read_fresh (x :: xs) _
where
  readFrom_length (b : Buffer α) : ∀ (s n : ℕ) (ys : List α),
      readFrom b s n = some ys → ys.length = n
    | _, 0, ys, h => by simp [readFrom] at h; subst h; rfl
    | s, n + 1, ys, h => by
      simp only [readFrom] at h
      split at h
      · next y zs _ hzs =>
        cases h
        simp [readFrom_length b (s + 1) n zs hzs]
      · cases h

/-- Every live view reads the same list after a prepend, whichever view the
prepend extended. -/
theorem read_stable {H : Heap α} {v w : View} {xs : List α} (x : α)
    (hw : Live H w) :
    read (prepend H v xs x).1 w = read H w := by
  unfold prepend
  split
  · next hc =>
    obtain ⟨hpos, hfront⟩ := hc
    simp only [read]
    by_cases haddr : w.addr = v.addr
    · rw [haddr, Function.update_self]
      refine readFrom_congr _ _ fun i h1 _ => ?_
      have hw' : (H.buf v.addr).front ≤ w.start := haddr ▸ hw.2
      simp only [claimBuffer]
      rw [Function.update_of_ne (by omega)]
    · rw [Function.update_of_ne haddr]
  · simp only [read]
    rw [Function.update_of_ne (Nat.ne_of_lt hw.1)]

/-- A live view stays live across a prepend, and the prepend's own view is
live. -/
theorem live_stable {H : Heap α} {v w : View} {xs : List α} (x : α)
    (hw : Live H w) : Live (prepend H v xs x).1 w := by
  unfold prepend
  split
  · next hc =>
    refine ⟨hw.1, ?_⟩
    by_cases haddr : w.addr = v.addr
    · simp only [haddr, Function.update_self, claimBuffer]
      have := haddr ▸ hw.2
      omega
    · simp only [Function.update_of_ne haddr]
      exact hw.2
  · refine ⟨Nat.lt_succ_of_lt hw.1, ?_⟩
    simp only [Function.update_of_ne (Nat.ne_of_lt hw.1)]
    exact hw.2

theorem live_prepend {H : Heap α} {v : View} {xs : List α} (x : α)
    (hv : Live H v) : Live (prepend H v xs x).1 (prepend H v xs x).2.1 := by
  unfold prepend
  split
  · next hc =>
    obtain ⟨_, hfront⟩ := hc
    refine ⟨hv.1, ?_⟩
    simp [claimBuffer, hfront]
  · refine ⟨Nat.lt_succ_self _, ?_⟩
    simp [fresh]

/-- The view a prepend returns starts at its buffer's front. -/
theorem front_prepend {H : Heap α} {v : View} {xs : List α} (x : α) :
    ((prepend H v xs x).1.buf (prepend H v xs x).2.1.addr).front =
      (prepend H v xs x).2.1.start := by
  unfold prepend
  split
  · next hc =>
    obtain ⟨_, hfront⟩ := hc
    simp [claimBuffer, hfront]
  · simp [fresh]

/-- A prepend that cannot claim copies the list and the new element. -/
theorem prepend_copy_cost {H : Heap α} {v : View} {xs : List α} (x : α)
    (h : ¬ Claimable H v) : (prepend H v xs x).2.2 = v.len + 1 := by
  simp [prepend, h]

/-! ## Sequential cost -/

/-- Prepend each element in turn, each onto the view the last prepend
returned: the final heap, view, and the slots written in all. -/
def run : Heap α → View → List α → List α → Heap α × View × ℕ
  | H, v, _, [] => (H, v, 0)
  | H, v, xs, y :: ys =>
    let r := prepend H v xs y
    let rest := run r.1 r.2.1 (y :: xs) ys
    (rest.1, rest.2.1, r.2.2 + rest.2.2)

/-- One prepend onto a view at its buffer's front with no more free slots
below it than elements costs at most three writes plus the drop in
`len - start`. -/
theorem prepend_cost {H : Heap α} {v : View} {xs : List α} (x : α)
    (hfront : (H.buf v.addr).front = v.start) (hle : v.start ≤ v.len) :
    (prepend H v xs x).2.2 + ((prepend H v xs x).2.1.len - (prepend H v xs x).2.1.start)
      ≤ 3 + (v.len - v.start) ∧
    (prepend H v xs x).2.1.start ≤ (prepend H v xs x).2.1.len := by
  unfold prepend
  split
  · next hc =>
    obtain ⟨hpos, _⟩ := hc
    exact ⟨by simp only; omega, by simp only; omega⟩
  · next hc =>
    have hzero : v.start = 0 := by
      rcases Nat.eq_zero_or_pos v.start with h | h
      · exact h
      · exact absurd ⟨h, hfront⟩ hc
    exact ⟨by simp only; omega, by simp only; omega⟩

/-- Along one chain of prepends the slots written are at most three per
element plus the chain's initial `len - start`. -/
theorem run_cost {H : Heap α} {v : View} {xs : List α} :
    ∀ (ys : List α), (H.buf v.addr).front = v.start → v.start ≤ v.len →
      (run H v xs ys).2.2 ≤ 3 * ys.length + (v.len - v.start)
  | [], _, _ => by simp [run]
  | y :: ys, hfront, hle => by
    obtain ⟨hstep, hle'⟩ := prepend_cost (xs := xs) y hfront hle
    have hrest := run_cost (H := (prepend H v xs y).1) (v := (prepend H v xs y).2.1)
      (xs := y :: xs) ys (front_prepend y) hle'
    simp only [run, List.length_cons]
    omega

/-- Along a chain, the final view reads the prepended elements, last first,
before the original list. -/
theorem read_run {H : Heap α} {v : View} {xs : List α} :
    ∀ (ys : List α), read H v = some xs →
      read (run H v xs ys).1 (run H v xs ys).2.1 = some (ys.reverse ++ xs)
  | [], h => by simpa [run] using h
  | y :: ys, h => by
    have := read_run (H := (prepend H v xs y).1) (v := (prepend H v xs y).2.1)
      (xs := y :: xs) ys (read_prepend y h)
    simpa [run] using this

/-! ## Branches pay for their own copies -/

/-- After one branch extends a view, the view is no longer at its buffer's
front, so a second branch prepending onto it copies. -/
theorem second_branch_copies {H : Heap α} {v : View} {xs : List α} (x x' : α)
    (hc : Claimable H v) (ys : List α) :
    ¬ Claimable (prepend H v xs x).1 v ∧
      (prepend (prepend H v xs x).1 v ys x').2.2 = v.len + 1 := by
  have hnot : ¬ Claimable (prepend H v xs x).1 v := by
    rintro ⟨_, hfront⟩
    obtain ⟨hpos, hfront0⟩ := hc
    simp only [prepend, if_pos (show Claimable H v from ⟨hpos, hfront0⟩),
      Function.update_self, claimBuffer, hfront0] at hfront
    omega
  exact ⟨hnot, prepend_copy_cost x' hnot⟩

/-- Both branches read their own lists: the first branch's extension is
untouched by the second branch's copy. -/
theorem branches_read {H : Heap α} {v : View} {xs : List α} (x x' : α)
    (hread : read H v = some xs) (hv : Live H v) :
    let first := prepend H v xs x
    let second := prepend first.1 v xs x'
    read second.1 first.2.1 = some (x :: xs) ∧
      read second.1 second.2.1 = some (x' :: xs) := by
  intro first second
  refine ⟨?_, ?_⟩
  · rw [read_stable (w := first.2.1) x' (live_prepend x hv)]
    exact read_prepend x hread
  · have hread' : read first.1 v = some xs := by
      rw [read_stable (w := v) x hv]; exact hread
    exact read_prepend x' hread'

/-- Negative control: writing the claimed slot again, as a second claim
without the front check would, changes the list the first branch reads. -/
theorem reclaim_breaks_first {H : Heap α} {v : View} {xs : List α} (x x' : α)
    (hne : x ≠ x') (hc : Claimable H v) :
    let first := prepend H v xs x
    let reclaimed : Heap α := { first.1 with
      buf := Function.update first.1.buf v.addr
        { cell := Function.update (first.1.buf v.addr).cell (v.start - 1) (some x'),
          front := v.start - 1 } }
    read reclaimed first.2.1 ≠ some (x :: xs) := by
  intro first reclaimed
  obtain ⟨hpos, hfront⟩ := hc
  have hview : first.2.1 = ⟨v.addr, v.start - 1, v.len + 1⟩ := by
    simp [first, prepend, show Claimable H v from ⟨hpos, hfront⟩]
  rw [hview]
  intro h
  simp only [read, reclaimed, Function.update_self, readFrom] at h
  split at h
  · next y ys hy _ =>
    simp only [Option.some.injEq] at hy
    cases h
    exact hne hy.symm
  · cases h

/-! ## Reading the front from the slots

A native buffer need not store its front.  Its free slots hold nothing and
its written slots hold something, so a view starts at the front exactly when
the slot just below it is free (`claimable_iff_free_below`).  A fresh buffer
is laid out that way (`fresh_packed`), and a claim keeps it so
(`claim_packed`).  A buffer whose lowest slot holds a marker that is never
free gives the native test the `0 < v.start` bound as well. -/

/-- The slots below the front are free, and those from the front up to `top`
are written. -/
def Packed (b : Buffer α) (top : ℕ) : Prop :=
  (∀ i, i < b.front → b.cell i = none) ∧
  (∀ i, b.front ≤ i → i < top → b.cell i ≠ none)

theorem fresh_packed (xs : List α) (slack : ℕ) :
    Packed (fresh xs slack) (slack + xs.length) := by
  refine ⟨fun i below => ?_, fun i above within => ?_⟩
  · simp only [fresh] at below ⊢
    rw [if_neg (by omega)]
  · simp only [fresh] at above ⊢
    rw [if_pos above]
    intro missing
    rw [List.getElem?_eq_none_iff] at missing
    omega

theorem claim_packed {b : Buffer α} {top : ℕ} (x : α)
    (packed : Packed b top) (positive : 0 < b.front) :
    Packed (claimBuffer b x) top := by
  obtain ⟨free, written⟩ := packed
  refine ⟨fun i below => ?_, fun i above within => ?_⟩
  · simp only [claimBuffer] at below ⊢
    rw [Function.update_of_ne (by omega)]
    exact free i (by omega)
  · simp only [claimBuffer] at above ⊢
    by_cases claimed : i = b.front - 1
    · rw [claimed, Function.update_self]
      exact Option.some_ne_none x
    · rw [Function.update_of_ne claimed]
      exact written i (by omega) within

/-- In a packed buffer, a view starts at the front exactly when the slot
below it is free. -/
theorem claimable_iff_free_below {H : Heap α} {v : View} {top : ℕ}
    (packed : Packed (H.buf v.addr) top)
    (live : (H.buf v.addr).front ≤ v.start) (within : v.start ≤ top) :
    Claimable H v ↔
      0 < v.start ∧ (H.buf v.addr).cell (v.start - 1) = none := by
  obtain ⟨free, written⟩ := packed
  constructor
  · rintro ⟨positive, atFront⟩
    exact ⟨positive, free (v.start - 1) (by omega)⟩
  · rintro ⟨positive, below⟩
    refine ⟨positive, ?_⟩
    by_contra notFront
    exact written (v.start - 1) (by omega) (by omega) below

/-! ## Examples -/

namespace Examples

/-- A heap holding `[1, 2, 3]` at slots 0 to 2 of buffer 0, with no free slot
below it. -/
def heap₀ : Heap ℕ where
  buf _ := fresh [1, 2, 3] 0
  next := 1

def view₀ : View := ⟨0, 0, 3⟩

theorem read₀ : read heap₀ view₀ = some [1, 2, 3] := rfl

/-- Four prepends: the first copies the three elements with three free slots
below them, the next three claim those slots. -/
theorem four_prepends :
    (run heap₀ view₀ [1, 2, 3] [4, 5, 6, 7]).2.2 = 4 + 1 + 1 + 1 ∧
      read (run heap₀ view₀ [1, 2, 3] [4, 5, 6, 7]).1
        (run heap₀ view₀ [1, 2, 3] [4, 5, 6, 7]).2.1 = some [7, 6, 5, 4, 1, 2, 3] := by
  refine ⟨by decide, read_run _ read₀⟩

end Examples

end Mettapedia.Machines.Cursor.PrefixBuffer
