import Mathlib.Tactic
import Mettapedia.Machines.RentOrBuyIndex

/-!
# Indexes restricted to one head: built from the head's rows

A query that binds a row's head and more of the row builds an index restricted
to that head.  Built by scanning every row of the space, one build costs the
space's `N` rows whatever the head holds, so the indexes of `q` heads cost
`q * N`: for `N` heads of one row each, all queried, `N * N`.  Built from the
head's own rows, which the head index lists, a build costs that head's rows,
so the builds for any set of heads cost at most `N`; and the indexes of
distinct heads hold disjoint rows, so together they hold at most the rows.
Deciding each head's index by the rent-or-buy rule with that head's prices
keeps each head within twice its best choice plus one rent, so all the heads
together stay within twice the sum of their best choices plus one rent a head.

The model: a space's rows by their heads, a list; the heads queried, a finite
set.  This file proves:
* `byHead_le_rows`: building from each head's rows costs at most `N` for any
  set of heads, which also bounds the rows the indexes hold;
* `one_row_heads`: `N` heads of one row each, all queried: `N * N` by scanning
  every row, `N` from the heads' rows;
* `heads_competitive`: the rent-or-buy rule per head, summed over the heads.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.HeadIndexCost

open Mettapedia.Machines.RentOrBuyIndex

variable {Head : Type} [DecidableEq Head]

/-- Building the index of each head of `q` by scanning every row. -/
def scanAllCost (rows : List Head) (q : Finset Head) : Nat :=
  q.card * rows.length

/-- Building the index of each head of `q` from that head's rows; the same sum
counts the rows those indexes hold. -/
def byHeadCost (rows : List Head) (q : Finset Head) : Nat :=
  ∑ h ∈ q, rows.count h

/-- Built from the heads' rows, the indexes of any set of heads cost, and
hold, at most the rows. -/
theorem byHead_le_rows (rows : List Head) (q : Finset Head) :
    byHeadCost rows q ≤ rows.length := by
  unfold byHeadCost
  calc ∑ h ∈ q, rows.count h
      ≤ ∑ h ∈ q ∪ rows.toFinset, rows.count h :=
        Finset.sum_le_sum_of_subset Finset.subset_union_left
    _ = ∑ h ∈ rows.toFinset, rows.count h := by
        refine (Finset.sum_subset Finset.subset_union_right ?_).symm
        intro h _ absent
        exact List.count_eq_zero.mpr (by simpa using absent)
    _ = rows.length := List.sum_toFinset_count_eq_length rows

/-- `N` heads of one row each, every one queried: scanning every row builds
in `N * N` steps, the heads' rows in `N`. -/
theorem one_row_heads (n : Nat) :
    scanAllCost (List.range n) (Finset.range n) = n * n ∧
      byHeadCost (List.range n) (Finset.range n) = n := by
  refine ⟨by simp [scanAllCost], ?_⟩
  unfold byHeadCost
  rw [Finset.sum_congr rfl (fun h hh => List.count_eq_one_of_mem
    List.nodup_range (List.mem_range.mpr (Finset.mem_range.mp hh)))]
  simp

omit [DecidableEq Head] in
/-- Each head's index decided by the rent-or-buy rule with its own prices and
probes: all the heads together pay at most twice the sum of their best
choices, plus one rent a head. -/
theorem heads_competitive (q : Finset Head) (p : Head → Prices)
    (k : Head → Nat) :
    ∑ h ∈ q, (run (p h) (k h)).2 ≤
      2 * ∑ h ∈ q, min (k h * (p h).rent) ((p h).buy + k h * (p h).use) +
        ∑ h ∈ q, (p h).rent := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun h _ => run_competitive (p h) (k h))

end Mettapedia.Machines.HeadIndexCost
