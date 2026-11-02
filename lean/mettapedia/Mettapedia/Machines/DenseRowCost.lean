import Mathlib.Tactic

/-!
# Rows kept in leaves: bytes in proportion to their numbers

A binary relation kept as bits holds a row of numbers for each number of its
first column.  A row kept as bits from 0 up to its largest number `m` takes
`8 * (m / 64 + 1)` bytes however few numbers it holds, so one far number
costs a row of 64 numbers bits up to it, and rows given one each take bytes
in proportion to the rows times the numbers: 2,000 rows of 64 small numbers,
each given one number past 400,000 others, took 128 MB more.

Rows are now kept in leaves by chunks of `2^16` numbers: sorted arrays of at
most 4,096 numbers, and a chunk's numbers as bits from the chunk's start
while they take fewer bytes so (the byte rule: `8 * (l / 64 + 1) < 4 * c`
for `c` numbers whose largest lies `l` past the chunk's start).  An array
doubles when full and halves once its count falls to a quarter of its
capacity; bits grow only under the byte rule, else the leaf is made anew;
bits that take over four times the bytes of their numbers as an array are
made anew; an emptied leaf goes.  A leaf made anew is an array of a power of
two of slots below twice its count, or bits under the byte rule.

The model: a leaf's count and storage, an array's slots or bits' words,
the power of two each step picks given by its bounds.  This file proves:
* `made_inv`, `inv_put`, `inv_take`: every leaf made, and every put and take
  from a leaf within the invariant, keeps a nonempty leaf within it;
* `inv_bytes`: such a leaf takes at most 16 bytes a number;
* `grow_refused_small`, `sparse_small`: bits made anew hold at most 2,047
  numbers, at most 1,024 words, so a step reads at most one leaf of at most
  4,096 numbers or 1,024 words;
* `row_bytes_le`: a row of leaves in a list kept within four times its
  length takes at most 112 bytes a number, plus 112, wherever its numbers lie;
* `far_rows_bits`, `far_rows_leaves` and `far_bits_exceed`: rows of 64
  numbers given one number `m` each take at least `rows * (m / 8)` bytes as
  bits up to it, and `rows * 80` in leaves whatever `m`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.DenseRowCost

/-- A leaf: an array of `count` numbers in `slots` slots of 4 bytes, or bits
of `words` words of 8 bytes holding `count` numbers. -/
inductive Leaf
  | array (count slots : ℕ)
  | bits (count words : ℕ)
  deriving DecidableEq

namespace Leaf

def count : Leaf → ℕ
  | array c _ => c
  | bits c _ => c

def bytes : Leaf → ℕ
  | array _ s => 4 * s
  | bits _ w => 8 * w

/-- A nonempty leaf as the store keeps it: an array of at most 4,096 numbers
whose slots are at most 2 or below four times its count; bits of at most a
chunk's 1,024 words within twice the bytes of their numbers as an array. -/
def Inv : Leaf → Prop
  | array c s => 1 ≤ c ∧ c ≤ s ∧ c ≤ 4096 ∧ (s ≤ 2 ∨ s < 4 * c)
  | bits c w => 1 ≤ c ∧ 1 ≤ w ∧ w ≤ 1024 ∧ 8 * w ≤ 16 * c

/-- A leaf made anew from its numbers: an array in a power of two of slots
from 2, below twice its count beyond that; or a chunk's bits under the byte
rule, a power of two of words at least `l / 64 + 1` and below twice it. -/
def Made : Leaf → Prop
  | array c s => 1 ≤ c ∧ c ≤ 4096 ∧ c ≤ s ∧ (s = 2 ∨ s < 2 * c)
  | bits c w => ∃ l, l < 65536 ∧ 8 * (l / 64 + 1) < 4 * c ∧
      l / 64 + 1 ≤ w ∧ w < 2 * (l / 64 + 1) ∧ w ≤ 1024

theorem made_inv (x : Leaf) (h : Made x) : Inv x := by
  cases x with
  | array c s =>
    simp only [Made] at h
    simp only [Inv]
    omega
  | bits c w =>
    obtain ⟨l, _, hrule, hw, hw2, hmax⟩ := h
    simp only [Inv]
    omega

theorem inv_bytes (x : Leaf) (h : Inv x) : x.bytes ≤ 16 * x.count := by
  cases x with
  | array c s =>
    simp only [Inv] at h
    simp only [bytes, count]
    omega
  | bits c w =>
    simp only [Inv] at h
    simp only [bytes, count]
    omega

/-- A put of a new number into a leaf, in place: an array with room, or one
full and doubled, below 4,096 numbers; bits within their words; bits grown
under the byte rule to a power of two of words at least the new number's
`l / 64 + 1`, below twice it, within the chunk. -/
inductive Put : Leaf → Leaf → Prop
  | room (c s : ℕ) (h : c < s) (hc : c + 1 ≤ 4096) :
      Put (array c s) (array (c + 1) s)
  | doubled (c : ℕ) (hc : c + 1 ≤ 4096) :
      Put (array c c) (array (c + 1) (2 * c))
  | set (c w : ℕ) : Put (bits c w) (bits (c + 1) w)
  | grown (c w l w' : ℕ) (rule : 8 * (l / 64 + 1) < 4 * (c + 1))
      (hw : l / 64 + 1 ≤ w') (hw2 : w' < 2 * (l / 64 + 1)) (hmax : w' ≤ 1024) :
      Put (bits c w) (bits (c + 1) w')

theorem inv_put (x y : Leaf) (hx : Inv x) (hput : Put x y) : Inv y := by
  cases hput with
  | room c s h hc =>
    simp only [Inv] at hx ⊢
    omega
  | doubled c hc =>
    simp only [Inv] at hx ⊢
    omega
  | set c w =>
    simp only [Inv] at hx ⊢
    omega
  | grown c w l w' rule hw hw2 hmax =>
    simp only [Inv] at hx ⊢
    omega

/-- A take of a held number from a leaf left nonempty, in place: an array,
its slots halved once its count is at most a quarter of them; bits not yet
four times the bytes of their numbers as an array. -/
inductive Take : Leaf → Leaf → Prop
  | kept (c s : ℕ) (hc : 2 ≤ c) (keep : ¬(2 < s ∧ 4 * (c - 1) ≤ s)) :
      Take (array c s) (array (c - 1) s)
  | halved (c s : ℕ) (hc : 2 ≤ c) (hs : 2 < s) (quarter : 4 * (c - 1) ≤ s) :
      Take (array c s) (array (c - 1) (s / 2))
  | cleared (c w : ℕ) (hc : 2 ≤ c) (dense : 8 * w ≤ 16 * (c - 1)) :
      Take (bits c w) (bits (c - 1) w)

theorem inv_take (x y : Leaf) (hx : Inv x) (htake : Take x y) : Inv y := by
  cases htake with
  | kept c s hc keep =>
    simp only [Inv] at hx ⊢
    omega
  | halved c s hc hs quarter =>
    simp only [Inv] at hx ⊢
    omega
  | cleared c w hc dense =>
    simp only [Inv] at hx ⊢
    omega

/-- Bits whose growth the byte rule refuses, made anew with the new number,
hold at most 2,048 numbers: the rule fails only for so few within a chunk. -/
theorem grow_refused_small (c l : ℕ) (hl : l < 65536)
    (refused : ¬(8 * (l / 64 + 1) < 4 * (c + 1))) : c + 1 ≤ 2048 := by
  omega

/-- Bits made anew after a take held fewer numbers than half their words:
at most 511 after a chunk's 1,024 words. -/
theorem sparse_small (c w : ℕ) (hx : Inv (bits c w))
    (sparse : 16 * (c - 1) < 8 * w) : c - 1 ≤ 511 := by
  simp only [Inv] at hx
  omega

end Leaf

/-- A row of leaves in a list: the leaves' bytes, and a list of `slots`
entries of 24 bytes and 16 more, unless one leaf stands in place. -/
def rowBytes (leaves : List Leaf) (slots : ℕ) : ℕ :=
  (leaves.map Leaf.bytes).sum + (if leaves.length = 1 then 0 else 16 + 24 * slots)

def rowCount (leaves : List Leaf) : ℕ := (leaves.map Leaf.count).sum

theorem leaves_bytes_le (leaves : List Leaf) (h : ∀ x ∈ leaves, Leaf.Inv x) :
    (leaves.map Leaf.bytes).sum ≤ 16 * rowCount leaves := by
  induction leaves with
  | nil => simp [rowCount]
  | cons x rest ih =>
    simp only [List.map_cons, List.sum_cons, rowCount] at ih ⊢
    have hx := Leaf.inv_bytes x (h x (by simp))
    have hrest := ih (fun y hy => h y (by simp [hy]))
    omega

theorem length_le_count (leaves : List Leaf) (h : ∀ x ∈ leaves, Leaf.Inv x) :
    leaves.length ≤ rowCount leaves := by
  induction leaves with
  | nil => simp [rowCount]
  | cons x rest ih =>
    simp only [List.length_cons, rowCount, List.map_cons, List.sum_cons] at ih ⊢
    have hx : 1 ≤ x.count := by
      have := h x (by simp)
      cases x <;> simp only [Leaf.Inv] at this <;> simp only [Leaf.count] <;> omega
    have hrest := ih (fun y hy => h y (by simp [hy]))
    omega

/-- A row of leaves within the invariant, its list within four times its
length or four slots, takes at most 112 bytes a number and 112 more. -/
theorem row_bytes_le (leaves : List Leaf) (slots : ℕ)
    (h : ∀ x ∈ leaves, Leaf.Inv x) (hslots : slots ≤ 4 ∨ slots < 4 * leaves.length) :
    rowBytes leaves slots ≤ 112 * rowCount leaves + 112 := by
  have hb := leaves_bytes_le leaves h
  have hl := length_le_count leaves h
  unfold rowBytes
  split_ifs <;> omega

/-- A row kept as bits from 0 up to its largest number `m`. -/
def bitsUpTo (m : ℕ) : ℕ := 8 * (m / 64 + 1)

/-- Rows of 64 numbers given one number `m` each, kept as bits up to it,
take at least `rows * (m / 8)` bytes: in proportion to how far `m` lies. -/
theorem far_rows_bits (rows m : ℕ) : rows * (m / 8) ≤ rows * bitsUpTo m := by
  apply Nat.mul_le_mul_left
  unfold bitsUpTo
  omega

/-- The same rows in leaves: their 64 numbers in a word of bits, the far
number in an array of 2 slots, a list of 2 entries: 80 bytes a row,
whatever `m`, within the invariant and `row_bytes_le`. -/
theorem far_rows_leaves (rows : ℕ) :
    rows * rowBytes [.bits 64 1, .array 1 2] 2 = rows * 80 ∧
      (∀ x ∈ [Leaf.bits 64 1, Leaf.array 1 2], Leaf.Inv x) := by
  have h80 : rowBytes [.bits 64 1, .array 1 2] 2 = 80 := by decide
  refine ⟨by rw [h80], ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> simp only [Leaf.Inv] <;> omega

/-- From `m = 640` on, bits up to the far number take more than the leaves,
and the gap grows with `m`. -/
theorem far_bits_exceed (rows m : ℕ) (hrows : 1 ≤ rows) (hm : 640 ≤ m) :
    rows * 80 < rows * bitsUpTo m := by
  apply Nat.mul_lt_mul_of_pos_left _ (by omega)
  unfold bitsUpTo
  omega

end Mettapedia.Machines.DenseRowCost
