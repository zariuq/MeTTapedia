import Mathlib.Tactic

/-!
# Pages of interned integers: kept forever, or freed as they empty

A store that interns integers can index them by pages of consecutive values.
A page holds the stored positions of its live integers, sparsely (a sorted
array of entries, grown by doubling) or densely (one slot per value of the
page, once it holds enough of them).

If a page is never released, a run that interns ever-new integers and lets
them die keeps every page it ever made: memory grows with the integers ever
seen, not with those alive.  Dense pages are the worst: one page costs its
whole slot array even with no live integer in it.

Releasing a page when it empties, returning a dense page to the sparse form
below a low-water mark `L` (it becomes dense at `H ≥ L`), and halving a sparse
array that falls to a quarter full bounds every page by a constant times its
live integers.

This file proves, for any page header cost, entry cost and dense array cost:
* `leaky_remove_ne_absent`, `leaky_dense_empty_cost`: without release a page
  once made stays, and an empty dense page keeps its whole array;
* `reachable_cost_le`: with release, `L * cost p ≤ k * live p` for every page
  reachable from nothing, where `k = L * header + 4 * L * entry + dense`;
* `reachable_empty_absent`: with release, a reachable page with no live
  integer is gone.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.IntegerPageCost

/-- A page: absent, sparse with `len` live entries in an array of `cap`, or
dense with `len` live integers. -/
inductive Page
  | absent
  | sparse (len cap : Nat)
  | dense (len : Nat)
  deriving DecidableEq

/-- The live integers of a page. -/
def live : Page → Nat
  | .absent => 0
  | .sparse len _ => len
  | .dense len => len

section Policy

-- The page becomes dense when an insertion finds `H` live entries, and
-- returns to sparse below `L`.
variable (H L : Nat)

/-- An insertion: a new page starts sparse with room for four; a full sparse
array doubles; a sparse page holding `H` goes dense. -/
def insert : Page → Page
  | .absent => .sparse 1 4
  | .sparse len cap =>
      if H ≤ len then .dense (len + 1)
      else if len = cap then .sparse (len + 1) (2 * cap)
      else .sparse (len + 1) cap
  | .dense len => .dense (len + 1)

/-- A removal that releases: an emptied page goes; a dense page below `L`
returns to a sparse array of `max 4 (2 * len)`; a sparse array a quarter full
halves. -/
def remove : Page → Page
  | .absent => .absent
  | .sparse len cap =>
      if len ≤ 1 then .absent
      else if 4 * (len - 1) ≤ cap ∧ 4 < cap then .sparse (len - 1) (cap / 2)
      else .sparse (len - 1) cap
  | .dense len =>
      if len ≤ 1 then .absent
      else if len - 1 < L then .sparse (len - 1) (max 4 (2 * (len - 1)))
      else .dense (len - 1)

/-- A removal that never releases: positions clear, pages stay. -/
def removeLeaky : Page → Page
  | .absent => .absent
  | .sparse len cap => .sparse (len - 1) cap
  | .dense len => .dense (len - 1)

/-- The pages reachable from nothing by insertions and releasing removals. -/
inductive Reachable : Page → Prop
  | absent : Reachable .absent
  | insert {p : Page} : Reachable p → Reachable (insert H p)
  | remove {p : Page} : Reachable p → Reachable (remove L p)

/-- The shape every reachable page keeps: a sparse page holds at least one
entry, within its array, and the array is at most `max 4 (4 * len)`; a dense
page holds at least `L`. -/
def Shape : Page → Prop
  | .absent => True
  | .sparse len cap => 1 ≤ len ∧ len ≤ cap ∧ cap ≤ max 4 (4 * len)
  | .dense len => L ≤ len

theorem shape_insert (hLH : L ≤ H) (p : Page) (hp : Shape L p) :
    Shape L (insert H p) := by
  cases p with
  | absent => simp [insert, Shape]
  | sparse len cap =>
    simp only [Shape] at hp
    simp only [insert]
    split_ifs with h1 h2
    · simp only [Shape]; omega
    · simp only [Shape]; omega
    · simp only [Shape]; omega
  | dense len =>
    simp only [Shape] at hp
    show L ≤ len + 1
    omega

theorem shape_remove (p : Page) (hp : Shape L p) : Shape L (remove L p) := by
  cases p with
  | absent => simp [remove, Shape]
  | sparse len cap =>
    simp only [Shape] at hp
    simp only [remove]
    split_ifs with h1 h2
    · simp [Shape]
    · simp only [Shape]
      obtain ⟨h4, h5⟩ := h2
      omega
    · simp only [Shape]
      omega
  | dense len =>
    simp only [Shape] at hp
    simp only [remove]
    split_ifs with h1 h2
    · simp [Shape]
    · simp only [Shape]; omega
    · simp only [Shape]; omega

theorem reachable_shape (hLH : L ≤ H) {p : Page} (hp : Reachable H L p) :
    Shape L p := by
  induction hp with
  | absent => simp [Shape]
  | insert _ ih => exact shape_insert H L hLH _ ih
  | remove _ ih => exact shape_remove L _ ih

/-- A reachable page with no live integer is gone. -/
theorem reachable_empty_absent (hLH : L ≤ H) (hL : 1 ≤ L) {p : Page}
    (hp : Reachable H L p) (h0 : live p = 0) : p = .absent := by
  have hs := reachable_shape H L hLH hp
  cases p with
  | absent => rfl
  | sparse len cap => simp only [Shape, live] at hs h0; omega
  | dense len => simp only [Shape, live] at hs h0; omega

end Policy

section Cost

/-- The bytes of a page: its header and slot, plus its sparse array or its
dense slot array. -/
def cost (header entry dense : Nat) : Page → Nat
  | .absent => 0
  | .sparse _ cap => header + entry * cap
  | .dense _ => header + dense

variable (H L header entry dense : Nat)

/-- With release, every reachable page costs at most a constant times its live
integers: `L * cost p ≤ (L * header + 4 * L * entry + dense) * live p`. -/
theorem reachable_cost_le (hLH : L ≤ H) {p : Page} (hp : Reachable H L p) :
    L * cost header entry dense p ≤
      (L * header + 4 * L * entry + dense) * live p := by
  have hs := reachable_shape H L hLH hp
  cases p with
  | absent => simp [cost]
  | sparse len cap =>
    simp only [Shape] at hs
    obtain ⟨h1, _, h3⟩ := hs
    have hcap : cap ≤ 4 * len := by omega
    simp only [cost, live]
    have e1 : entry * cap ≤ entry * (4 * len) := Nat.mul_le_mul_left entry hcap
    have e2 : header ≤ header * len := Nat.le_mul_of_pos_right header h1
    nlinarith
  | dense len =>
    simp only [Shape] at hs
    simp only [cost, live]
    rcases Nat.eq_zero_or_pos L with hL | hL
    · -- `L = 0`: the left side is zero.
      subst hL; simp
    · have hpos : 1 ≤ len := by omega
      have d1 : L * dense ≤ len * dense := Nat.mul_le_mul_right dense hs
      have d2 : L * header ≤ L * (header * len) :=
        Nat.mul_le_mul_left L (Nat.le_mul_of_pos_right header hpos)
      have expand : (L * header + 4 * L * entry + dense) * len =
          L * (header * len) + len * dense + 4 * L * entry * len := by ring
      calc L * (header + dense) = L * header + L * dense := by ring
        _ ≤ L * (header * len) + len * dense := Nat.add_le_add d2 d1
        _ ≤ (L * header + 4 * L * entry + dense) * len := by
          rw [expand]; exact Nat.le_add_right _ _

/-- Without release a page once made never goes. -/
theorem leaky_remove_ne_absent (p : Page) (hp : p ≠ .absent) :
    removeLeaky p ≠ .absent := by
  cases p with
  | absent => exact absurd rfl hp
  | sparse len cap => simp [removeLeaky]
  | dense len => simp [removeLeaky]

/-- Without release an emptied dense page keeps its whole slot array. -/
theorem leaky_dense_empty_cost :
    live (removeLeaky (.dense 1)) = 0 ∧
      cost header entry dense (removeLeaky (.dense 1)) = header + dense := by
  simp [removeLeaky, live, cost]

/-- With release, the same page is gone. -/
theorem release_dense_one : remove L (.dense 1) = .absent := by
  simp [remove]

end Cost

end Mettapedia.Machines.IntegerPageCost
