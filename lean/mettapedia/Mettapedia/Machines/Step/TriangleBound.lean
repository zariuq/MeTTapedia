import Mettapedia.Machines.Step.SeekerJoin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The triangle query: the square-root bound, for the answers and for the work

For the query `R(a, b), S(b, c), T(a, c)` write `deg S b` for the number of
pairs of `S` that begin with `b`.  A join that has bound `a` and `b` from a pair
of `R` must find the `c` common to `S`'s row of `b` and `T`'s row of `a`.  The
*min rule* reads the shorter row and searches the longer: its work at the pair
is `min (deg S b) (deg T a)` (`visit`).

* `sum_visit_sq_le`: over all pairs of `R` the min rule's work, squared, is at
  most `|R| * |S| * |T|`.  So the work is at most the square root of the
  product, on every instance.
* `triangle_answers_sq_le`: the answers of the triangle seeker of `SeekerJoin`,
  squared, are at most `|R| * |S| * |T|`: no instance has more than
  `sqrt (|R| * |S| * |T|)` triangles.  The bound on the work is therefore of
  the order of the largest possible answer.
* `thirdLevelSeeks_le`, `thirdLevelSeeks_sq_le`: the searches the leapfrog of
  `SeekerJoin` actually makes for the third variable, the shorter row read
  first, are at most `2 * sqrt (|R| * |S| * |T|) + |R|`.
* `star_fixed_first`, `star_fixed_second`, `star_min`: on the star with `n`
  leaves (`|R| = |S| = |T| = 2 * n`) a nested loop that always reads `S`'s row
  and probes `T` makes `n * n + n` probes, the one that always reads `T`'s row
  makes as many, and the min rule makes `2 * n`.  No fixed choice of the leg to
  read is within a constant of the min rule.

The first two variables cost at most `2 * |R| + 1` searches each level by
`Seeker.interDrainSeeks_le`, summed over the outer keys; that linear part is
not restated here.  What is not proved here: a bound of this kind for an
arbitrary conjunctive query (the fractional edge cover bound), and the cost of
resuming the stateless seeker of `SeekerJoin` from an answer, which adds two
searches per level and answer to the figures above.

Positive example: `Controls.min_rule_example`.  Negative example:
`Controls.product_bound_fails_for_fixed` (the fixed leg's work on the star with
three leaves exceeds the square-root bound).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.TriangleBound

open Finset Seeker

variable {K : Type*} [LinearOrder K]

/-- The pairs of `S` that begin with `b`. -/
def deg (S : Finset (K × K)) (b : K) : ℕ := (S.filter fun p => p.1 = b).card

theorem card_row (S : Finset (K × K)) (b : K) : (row S b).card = deg S b := by
  unfold row deg
  apply Finset.card_image_of_injOn
  intro p hp q hq h
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  exact Prod.ext (hp'.trans hq'.symm) h

/-- Rows of distinct first components are disjoint parts of the relation. -/
theorem sum_deg_le (S : Finset (K × K)) (B : Finset K) : ∑ b ∈ B, deg S b ≤ S.card := by
  unfold deg
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact Finset.card_filter_le _ _

/-- The min rule's work at a pair `(a, b)` of `R`: the shorter of `S`'s row of
`b` and `T`'s row of `a`. -/
def visit (S T : Finset (K × K)) (p : K × K) : ℕ := min (deg S p.2) (deg T p.1)

/-- **The square-root bound for the work.** -/
theorem sum_visit_sq_le (R S T : Finset (K × K)) :
    (∑ p ∈ R, visit S T p) ^ 2 ≤ R.card * S.card * T.card := by
  calc (∑ p ∈ R, visit S T p) ^ 2
      ≤ R.card * ∑ p ∈ R, visit S T p ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ R.card * ∑ p ∈ R, deg S p.2 * deg T p.1 := by
        apply Nat.mul_le_mul_left
        apply Finset.sum_le_sum
        intro p _
        unfold visit
        rw [sq]
        exact Nat.mul_le_mul (min_le_left _ _) (min_le_right _ _)
    _ ≤ R.card * ∑ p ∈ R.image Prod.fst ×ˢ R.image Prod.snd, deg S p.2 * deg T p.1 := by
        apply Nat.mul_le_mul_left
        apply Finset.sum_le_sum_of_subset
        intro p hp
        exact Finset.mem_product.mpr
          ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    _ = R.card * ((∑ b ∈ R.image Prod.snd, deg S b) * ∑ a ∈ R.image Prod.fst, deg T a) := by
        rw [Finset.sum_mul_sum, Finset.sum_product, Finset.sum_comm]
    _ ≤ R.card * (S.card * T.card) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (sum_deg_le S _) (sum_deg_le T _))
    _ = R.card * S.card * T.card := by ring

/-- A pair of `R` with a common successor in `S` and `T`: a triangle. -/
def wedges (R S T : Finset (K × K)) : Finset (Σ _ : K × K, K) :=
  R.sigma fun p => row S p.2 ∩ row T p.1

theorem card_wedges_le (R S T : Finset (K × K)) :
    (wedges R S T).card ≤ ∑ p ∈ R, visit S T p := by
  rw [wedges, Finset.card_sigma]
  apply Finset.sum_le_sum
  intro p _
  unfold visit
  rw [← card_row, ← card_row]
  exact le_min (Finset.card_le_card Finset.inter_subset_left)
    (Finset.card_le_card Finset.inter_subset_right)

/-- **The square-root bound for the answers**, stated for the triangle seeker:
whatever lawful index it reads, it holds at most `sqrt (|R| * |S| * |T|)`
answers. -/
theorem triangle_answers_sq_le (index : Finset K → Seeker K)
    (lawful : ∀ s, (index s).keys = s) (R S T : Finset (K × K)) :
    (triangle index R S T).keys.card ^ 2 ≤ R.card * S.card * T.card := by
  have inj : (triangle index R S T).keys.card ≤ (wedges R S T).card := by
    refine Finset.card_le_card_of_injOn
      (fun t => ⟨((ofLex t).1, (ofLex (ofLex t).2).1), (ofLex (ofLex t).2).2⟩) ?_ ?_
    · intro t ht
      obtain ⟨⟨a, q⟩, rfl⟩ := toLex.surjective t
      obtain ⟨⟨b, c⟩, rfl⟩ := toLex.surjective q
      have mem := (mem_triangle_keys index lawful R S T a b c).mp ht
      simp only [wedges, Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe,
        Finset.mem_inter, mem_row, ofLex_toLex]
      exact ⟨mem.1, mem.2.1, mem.2.2⟩
    · intro t _ t' _ eq
      obtain ⟨⟨a, q⟩, rfl⟩ := toLex.surjective t
      obtain ⟨⟨b, c⟩, rfl⟩ := toLex.surjective q
      obtain ⟨⟨a', q'⟩, rfl⟩ := toLex.surjective t'
      obtain ⟨⟨b', c'⟩, rfl⟩ := toLex.surjective q'
      simp only [ofLex_toLex, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at eq
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := eq
      rfl
  calc (triangle index R S T).keys.card ^ 2
      ≤ (∑ p ∈ R, visit S T p) ^ 2 :=
        Nat.pow_le_pow_left (inj.trans (card_wedges_le R S T)) 2
    _ ≤ R.card * S.card * T.card := sum_visit_sq_le R S T

/-- The searches the leapfrog spends on the third variable at the pair `p`:
a whole drain of the intersection of the two rows, the shorter read first. -/
def pairSeeks (index : Finset K → Seeker K) (S T : Finset (K × K)) (p : K × K) : ℕ :=
  if deg S p.2 ≤ deg T p.1 then
    interDrainSeeks (index (row S p.2)) (index (row T p.1)) .all
  else
    interDrainSeeks (index (row T p.1)) (index (row S p.2)) .all

theorem pairSeeks_le (index : Finset K → Seeker K) (lawful : ∀ s, (index s).keys = s)
    (S T : Finset (K × K)) (p : K × K) : pairSeeks index S T p ≤ 2 * visit S T p + 1 := by
  unfold pairSeeks visit
  split
  · rename_i h
    have cost := interDrainSeeks_le (index (row S p.2)) (index (row T p.1)) .all
    have size : ((index (row S p.2)).keys.filter (Bound.all : Bound K).admits).card ≤
        deg S p.2 := by
      rw [← card_row, lawful]
      exact Finset.card_filter_le _ _
    rw [min_eq_left h]
    omega
  · rename_i h
    have cost := interDrainSeeks_le (index (row T p.1)) (index (row S p.2)) .all
    have size : ((index (row T p.1)).keys.filter (Bound.all : Bound K).admits).card ≤
        deg T p.1 := by
      rw [← card_row, lawful]
      exact Finset.card_filter_le _ _
    rw [min_eq_right (le_of_lt (not_le.mp h))]
    omega

/-- All the searches spent on the third variable. -/
def thirdLevelSeeks (index : Finset K → Seeker K) (R S T : Finset (K × K)) : ℕ :=
  ∑ p ∈ R, pairSeeks index S T p

theorem thirdLevelSeeks_le (index : Finset K → Seeker K) (lawful : ∀ s, (index s).keys = s)
    (R S T : Finset (K × K)) :
    thirdLevelSeeks index R S T ≤ 2 * (∑ p ∈ R, visit S T p) + R.card := by
  unfold thirdLevelSeeks
  calc ∑ p ∈ R, pairSeeks index S T p
      ≤ ∑ p ∈ R, (2 * visit S T p + 1) :=
        Finset.sum_le_sum fun p _ => pairSeeks_le index lawful S T p
    _ = 2 * (∑ p ∈ R, visit S T p) + R.card := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]

/-- **The square-root bound for the searches of the machine**: beyond one
search for each pair of `R`, the leapfrog spends at most
`2 * sqrt (|R| * |S| * |T|)` searches on the third variable. -/
theorem thirdLevelSeeks_sq_le (index : Finset K → Seeker K)
    (lawful : ∀ s, (index s).keys = s) (R S T : Finset (K × K)) :
    (thirdLevelSeeks index R S T - R.card) ^ 2 ≤ 4 * (R.card * S.card * T.card) := by
  have h := thirdLevelSeeks_le index lawful R S T
  calc (thirdLevelSeeks index R S T - R.card) ^ 2
      ≤ (2 * ∑ p ∈ R, visit S T p) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = 4 * (∑ p ∈ R, visit S T p) ^ 2 := by ring
    _ ≤ 4 * (R.card * S.card * T.card) := Nat.mul_le_mul_left _ (sum_visit_sq_le R S T)

/-! ## The star: no fixed leg is within a constant of the min rule -/

/-- A nested loop that always reads `S`'s row of `b` and probes `T`. -/
def fixedFirst (R S : Finset (K × K)) : ℕ := ∑ p ∈ R, deg S p.2

/-- A nested loop that always reads `T`'s row of `a` and probes `S`. -/
def fixedSecond (R T : Finset (K × K)) : ℕ := ∑ p ∈ R, deg T p.1

theorem sum_visit_le_fixed (R S T : Finset (K × K)) :
    ∑ p ∈ R, visit S T p ≤ fixedFirst R S ∧ ∑ p ∈ R, visit S T p ≤ fixedSecond R T :=
  ⟨Finset.sum_le_sum fun _ _ => min_le_left _ _, Finset.sum_le_sum fun _ _ => min_le_right _ _⟩

/-- The edges out of the hub `0` to the leaves `1, …, n`. -/
def spokesOut (n : ℕ) : Finset (ℕ × ℕ) := (Finset.range n).image fun i => (0, i + 1)

/-- The edges from the leaves into the hub. -/
def spokesIn (n : ℕ) : Finset (ℕ × ℕ) := (Finset.range n).image fun i => (i + 1, 0)

/-- The star with `n` leaves. -/
def star (n : ℕ) : Finset (ℕ × ℕ) := spokesOut n ∪ spokesIn n

theorem mem_star (n : ℕ) (p : ℕ × ℕ) :
    p ∈ star n ↔ (p.1 = 0 ∧ 1 ≤ p.2 ∧ p.2 ≤ n) ∨ (p.2 = 0 ∧ 1 ≤ p.1 ∧ p.1 ≤ n) := by
  obtain ⟨a, b⟩ := p
  simp only [star, spokesOut, spokesIn, Finset.mem_union, Finset.mem_image, Finset.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro (⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, by omega, by omega⟩
    · exact Or.inr ⟨rfl, by omega, by omega⟩
  · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
    · exact Or.inl ⟨b - 1, by omega, rfl, by omega⟩
    · exact Or.inr ⟨a - 1, by omega, by omega, rfl⟩

theorem deg_star_zero (n : ℕ) : deg (star n) 0 = n := by
  unfold deg
  have : (star n).filter (fun p => p.1 = 0) = spokesOut n := by
    ext p
    rw [Finset.mem_filter, mem_star]
    obtain ⟨a, b⟩ := p
    simp only [spokesOut, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨h | h, rfl⟩
      · exact ⟨b - 1, by omega, rfl, by omega⟩
      · omega
    · rintro ⟨i, hi, rfl, rfl⟩
      exact ⟨Or.inl ⟨rfl, by omega, by omega⟩, rfl⟩
  rw [this, spokesOut, Finset.card_image_of_injective _ (fun i j h => by simpa using h),
    Finset.card_range]

theorem deg_star_leaf (n j : ℕ) (pos : 1 ≤ j) (le : j ≤ n) : deg (star n) j = 1 := by
  unfold deg
  have : (star n).filter (fun p => p.1 = j) = {(j, 0)} := by
    ext p
    rw [Finset.mem_filter, mem_star, Finset.mem_singleton]
    obtain ⟨a, b⟩ := p
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨h | h, rfl⟩
      · omega
      · exact ⟨rfl, h.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inr ⟨rfl, pos, le⟩, rfl⟩
  rw [this, Finset.card_singleton]

theorem disjoint_spokes (n : ℕ) : Disjoint (spokesOut n) (spokesIn n) := by
  rw [Finset.disjoint_left]
  intro p h1 h2
  simp only [spokesOut, spokesIn, Finset.mem_image, Finset.mem_range] at h1 h2
  obtain ⟨i, _, rfl⟩ := h1
  obtain ⟨j, _, h⟩ := h2
  simp only [Prod.mk.injEq] at h
  omega

/-- A sum over the star: the spokes out, then the spokes in. -/
theorem sum_star (n : ℕ) (f : ℕ × ℕ → ℕ) :
    ∑ p ∈ star n, f p =
      ∑ i ∈ Finset.range n, f (0, i + 1) + ∑ i ∈ Finset.range n, f (i + 1, 0) := by
  rw [star, Finset.sum_union (disjoint_spokes n), spokesOut, spokesIn,
    Finset.sum_image (fun i _ j _ h => by simpa using h),
    Finset.sum_image (fun i _ j _ h => by simpa using h)]

theorem card_star (n : ℕ) : (star n).card = 2 * n := by
  have := sum_star n fun _ => 1
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range] at this
  omega

/-- Always reading `S`'s row: each spoke into the hub reads the hub's `n` rows. -/
theorem star_fixed_first (n : ℕ) : fixedFirst (star n) (star n) = n * n + n := by
  unfold fixedFirst
  rw [sum_star]
  have out : ∑ i ∈ Finset.range n, deg (star n) (i + 1) = n := by
    rw [Finset.sum_congr rfl fun i hi =>
      deg_star_leaf n (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)]
    simp
  have into : ∑ _i ∈ Finset.range n, deg (star n) 0 = n * n := by
    simp [deg_star_zero]
  simp only [out, into]
  omega

/-- Always reading `T`'s row: each spoke out of the hub reads the hub's `n` rows. -/
theorem star_fixed_second (n : ℕ) : fixedSecond (star n) (star n) = n * n + n := by
  unfold fixedSecond
  rw [sum_star]
  have out : ∑ _i ∈ Finset.range n, deg (star n) 0 = n * n := by
    simp [deg_star_zero]
  have into : ∑ i ∈ Finset.range n, deg (star n) (i + 1) = n := by
    rw [Finset.sum_congr rfl fun i hi =>
      deg_star_leaf n (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)]
    simp
  simp only [out, into]

/-- The min rule reads one row at every pair of the star. -/
theorem star_min (n : ℕ) : ∑ p ∈ star n, visit (star n) (star n) p = 2 * n := by
  rw [sum_star]
  have each : ∀ i ∈ Finset.range n, visit (star n) (star n) (0, i + 1) = 1 ∧
      visit (star n) (star n) (i + 1, 0) = 1 := by
    intro i hi
    have lt := Finset.mem_range.mp hi
    unfold visit
    simp only [deg_star_zero, deg_star_leaf n (i + 1) (by omega) (by omega)]
    exact ⟨min_eq_left (by omega), min_eq_right (by omega)⟩
  rw [Finset.sum_congr rfl fun i hi => (each i hi).1,
    Finset.sum_congr rfl fun i hi => (each i hi).2]
  simp
  omega

/-- **The gap on the star.**  With `N = |R| = |S| = |T| = 2 * n`, either fixed
leg costs `n * n + n`, a quarter of `N * N`, and the min rule costs `N`. -/
theorem star_gap (n : ℕ) :
    (star n).card = 2 * n ∧ fixedFirst (star n) (star n) = n * n + n ∧
      fixedSecond (star n) (star n) = n * n + n ∧
      ∑ p ∈ star n, visit (star n) (star n) p = 2 * n :=
  ⟨card_star n, star_fixed_first n, star_fixed_second n, star_min n⟩

namespace Controls

/-- Positive: on the star with three leaves the min rule's work, squared, is
within the product of the sizes. -/
theorem min_rule_example :
    (∑ p ∈ star 3, visit (star 3) (star 3) p) ^ 2 ≤ (star 3).card * (star 3).card * (star 3).card :=
  sum_visit_sq_le _ _ _

/-- Negative: the fixed leg's work on the star with eight leaves, squared,
exceeds the product of the sizes: the square-root bound is not a bound for it. -/
theorem product_bound_fails_for_fixed :
    ¬ fixedFirst (star 8) (star 8) ^ 2 ≤ (star 8).card * (star 8).card * (star 8).card := by
  rw [star_fixed_first, card_star]
  decide

end Controls

end Mettapedia.Machines.Step.TriangleBound
