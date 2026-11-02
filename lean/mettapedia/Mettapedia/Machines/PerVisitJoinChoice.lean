import Mathlib.Tactic

/-!
# Choosing a join leg once, or at every visit

A join depth whose two remaining legs bind the same new variable can read either
leg and test each answer against the other: both give the intersection.  A visit
costs the size of the leg it reads.  Deciding the leg at the first visit and
keeping it costs, over all visits, the sum of that leg's sizes; choosing at every
visit, by counting both legs first, costs the sum of the smaller sizes plus the
counts.

On a star (a hub with an edge to and from each of `n` leaves, and a ring through
the leaves), the triangle query's second depth meets three kinds of visit: the
hub's out-edges against a leaf's two in-edges, a leaf's two out-edges against the
hub's in-edges, and two against two.  Whichever leg a fixed choice keeps, one
kind of visit pays `n` each time, `n` times: no first decision is right.
Choosing per visit pays two each time.

This file proves:
* `iterate_either`: reading either leg and testing against the other gives the
  same answers;
* `perVisit_le_fixed`: choosing per visit costs no more than either fixed choice,
  counts aside;
* `star_fixed` and `star_perVisit`: on the star both fixed choices cost
  `n * n + 4 * n`, choosing per visit `6 * n` (and `12 * n` with two counts a
  visit).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PerVisitJoinChoice

/-- Reading `xs` and keeping what `ys` holds, or the other way round, gives the
same answers: the intersection. -/
theorem iterate_either (xs ys : Finset Nat) :
    xs.filter (· ∈ ys) = ys.filter (· ∈ xs) := by
  ext x; simp [and_comm]

/-- A visit: the sizes of the two legs it may read. -/
abbrev Visit := Nat × Nat

/-- Keeping the first leg at every visit. -/
def fixedFirst (vs : List Visit) : Nat := (vs.map Prod.fst).sum

/-- Keeping the second leg at every visit. -/
def fixedSecond (vs : List Visit) : Nat := (vs.map Prod.snd).sum

/-- Reading the smaller leg at each visit. -/
def perVisit (vs : List Visit) : Nat := (vs.map fun v => min v.1 v.2).sum

/-- Choosing per visit, with the two counts a visit takes. -/
def perVisitCounted (vs : List Visit) : Nat := perVisit vs + 2 * vs.length

theorem perVisit_le_fixed (vs : List Visit) :
    perVisit vs ≤ fixedFirst vs ∧ perVisit vs ≤ fixedSecond vs := by
  induction vs with
  | nil => simp [perVisit, fixedFirst, fixedSecond]
  | cons v vs ih =>
    simp only [perVisit, fixedFirst, fixedSecond, List.map_cons, List.sum_cons] at ih ⊢
    exact ⟨Nat.add_le_add (min_le_left _ _) ih.1, Nat.add_le_add (min_le_right _ _) ih.2⟩

/-- The star's visits at the triangle query's second depth, for `n` leaves: an
edge into the hub (the hub's `n` out-edges against the leaf's two in-edges), an
edge out of the hub (the leaf's two out-edges against the hub's `n` in-edges),
and a ring edge (two against two), `n` of each. -/
def star (n : Nat) : List Visit :=
  List.replicate n (n, 2) ++ List.replicate n (2, n) ++ List.replicate n (2, 2)

theorem star_fixed (n : Nat) :
    fixedFirst (star n) = n * n + 4 * n ∧ fixedSecond (star n) = n * n + 4 * n := by
  simp only [fixedFirst, fixedSecond, star, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate, smul_eq_mul]
  constructor <;> ring

theorem star_perVisit (n : Nat) (hn : 2 ≤ n) :
    perVisit (star n) = 6 * n ∧ perVisitCounted (star n) = 12 * n := by
  have h1 : min n 2 = 2 := min_eq_right hn
  have h2 : min 2 n = 2 := min_eq_left hn
  simp only [perVisitCounted, perVisit, star, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate, smul_eq_mul, h1, h2, List.length_append,
    List.length_replicate, min_self]
  constructor <;> ring

end Mettapedia.Machines.PerVisitJoinChoice
