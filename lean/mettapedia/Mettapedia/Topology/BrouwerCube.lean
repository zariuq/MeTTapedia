import Mettapedia.Combinatorics.Kuhn.Parity
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Brouwer's fixed-point theorem for cubes

Every continuous map of the cube `[0, 1]^n` into itself has a fixed point.

The proof is Kuhn's (1960). Suppose `f` has no fixed point. By compactness
`f x` and `x` stay a distance `d > 0` apart, and `f` is uniformly continuous.
Take a grid so fine that `f` moves by less than `d / 2` within a cell. Flag
coordinate `i` of a grid point `true` when `f` does not increase it there, and
`false` when `f` does not decrease it. On the face where the coordinate is `0`
the flag can be taken `false`, on the face where it is `1` it can be taken
`true`. Kuhn's lemma (`Combinatorics/Kuhn/Parity.lean`) gives a cell that has
both flags on every coordinate. At the corner of that cell `f` then changes
every coordinate by less than `d`: a contradiction.

## Main statements

* `brouwer_cube`: `∀ n (f : (Fin n → I) → (Fin n → I)), Continuous f → ∃ x, f x = x`.
* `brouwer_cube_fintype`: the same for the cube over any finite index type.

## References

* Kuhn (1960). "Some combinatorial lemmas in topology", IBM Journal 4.
* The Isabelle/HOL formalization `HOL-Analysis/Brouwer_Fixpoint` (Harrison;
  Himmelmann; Hölzl; Paulson) follows the same paper.
-/

set_option autoImplicit false

namespace Mettapedia.Topology

open Set Metric Mettapedia.Combinatorics.Kuhn
open scoped unitInterval

variable {n : ℕ}

/-- The point of the cube with coordinates `x i / (q + 1)`, cut off at `1`. -/
noncomputable def gridPoint (q : ℕ) (x : Fin n → ℕ) : Fin n → I :=
  fun i => projIcc (0 : ℝ) 1 zero_le_one ((x i : ℝ) / ((q : ℝ) + 1))

theorem coe_gridPoint (q : ℕ) (x : Fin n → ℕ) (i : Fin n) (inGrid : x i ≤ q + 1) :
    (gridPoint q x i : ℝ) = (x i : ℝ) / ((q : ℝ) + 1) := by
  have positive : (0 : ℝ) < (q : ℝ) + 1 := Nat.cast_add_one_pos q
  have nonneg : (0 : ℝ) ≤ (x i : ℝ) / ((q : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) positive.le
  have atMost : (x i : ℝ) / ((q : ℝ) + 1) ≤ 1 := by
    rw [div_le_one positive]
    exact_mod_cast inGrid
  simp only [gridPoint, coe_projIcc, min_eq_right atMost, max_eq_right nonneg]

theorem gridPoint_of_eq_zero (q : ℕ) (x : Fin n → ℕ) (i : Fin n) (zero : x i = 0) :
    (gridPoint q x i : ℝ) = 0 := by
  rw [coe_gridPoint q x i (by omega), zero, Nat.cast_zero, zero_div]

theorem gridPoint_of_eq_top (q : ℕ) (x : Fin n → ℕ) (i : Fin n) (top : x i = q + 1) :
    (gridPoint q x i : ℝ) = 1 := by
  have positive : (0 : ℝ) < (q : ℝ) + 1 := Nat.cast_add_one_pos q
  rw [coe_gridPoint q x i (by omega), top]
  push_cast
  exact div_self positive.ne'

/-- The corners of a cell lie within `1 / (q + 1)` of its lower corner. -/
theorem dist_gridPoint_le (q : ℕ) (base : Fin n → Fin (q + 1)) (r : Fin n → ℕ)
    (inCell : ∀ j, (base j : ℕ) ≤ r j ∧ r j ≤ base j + 1) :
    dist (gridPoint q r) (gridPoint q fun j => (base j : ℕ)) ≤ 1 / ((q : ℝ) + 1) := by
  have positive : (0 : ℝ) < (q : ℝ) + 1 := Nat.cast_add_one_pos q
  refine (dist_pi_le_iff (by positivity)).mpr fun j => ?_
  have bound := (base j).2
  have lower := (inCell j).1
  have upper := (inCell j).2
  rw [Subtype.dist_eq, Real.dist_eq, coe_gridPoint q r j (by omega),
    coe_gridPoint q (fun j => (base j : ℕ)) j (by omega), ← sub_div, abs_div, abs_of_pos positive,
    div_le_div_iff_of_pos_right positive, abs_le]
  constructor
  · have : ((base j : ℕ) : ℝ) ≤ (r j : ℝ) := by exact_mod_cast lower
    linarith
  · have : (r j : ℝ) ≤ ((base j : ℕ) : ℝ) + 1 := by exact_mod_cast upper
    linarith

/-- **Brouwer's fixed-point theorem for the cube `[0, 1]^n`.** -/
theorem brouwer_cube (n : ℕ) (f : (Fin n → I) → (Fin n → I)) (continuous : Continuous f) :
    ∃ x, f x = x := by
  by_contra none
  have moves : ∀ x, f x ≠ x := fun x same => none ⟨x, same⟩
  -- `f x` and `x` stay a positive distance apart
  obtain ⟨least, _, isLeast⟩ := (isCompact_univ (X := Fin n → I)).exists_isMinOn
    ⟨fun _ => 0, mem_univ _⟩ ((continuous.dist continuous_id).continuousOn)
  set d := dist (f least) least with d_def
  have d_pos : 0 < d := dist_pos.mpr (moves least)
  have apart : ∀ x, d ≤ dist (f x) x := fun x => isLeast (mem_univ x)
  -- `f` is uniformly continuous
  obtain ⟨δ, δ_pos, close⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous continuous) (d / 2) (by positivity)
  -- a grid finer than both
  obtain ⟨q, fine⟩ := exists_nat_one_div_lt (lt_min δ_pos (half_pos d_pos))
  have fineδ : 1 / ((q : ℝ) + 1) < δ := lt_of_lt_of_le fine (min_le_left _ _)
  have fined : 1 / ((q : ℝ) + 1) < d / 2 := lt_of_lt_of_le fine (min_le_right _ _)
  -- the flags
  let flag : (Fin n → ℕ) → Fin n → Bool := fun x i =>
    decide (x i ≠ 0 ∧ (f (gridPoint q x) i : ℝ) ≤ (gridPoint q x i : ℝ))
  have flagFalse : ∀ x i, flag x i = false → (gridPoint q x i : ℝ) ≤ (f (gridPoint q x) i : ℝ) := by
    intro x i isFalse
    have notBoth : ¬(x i ≠ 0 ∧ (f (gridPoint q x) i : ℝ) ≤ (gridPoint q x i : ℝ)) :=
      of_decide_eq_false isFalse
    by_cases zero : x i = 0
    · rw [gridPoint_of_eq_zero q x i zero]
      exact (f (gridPoint q x) i).2.1
    · exact le_of_lt (lt_of_not_ge fun le => notBoth ⟨zero, le⟩)
  have flagTrue : ∀ x i, flag x i = true → (f (gridPoint q x) i : ℝ) ≤ (gridPoint q x i : ℝ) :=
    fun x i isTrue => (of_decide_eq_true isTrue).2
  obtain ⟨base, both⟩ := exists_cell_with_both_labels q n flag
    (fun x i zero => decide_eq_false fun both => both.1 zero)
    (fun x i top => decide_eq_true ⟨by omega, by
      rw [gridPoint_of_eq_top q x i top]
      exact (f (gridPoint q x) i).2.2⟩)
  -- at the lower corner of that cell every coordinate moves by less than `d`
  set corner := gridPoint q fun j => (base j : ℕ) with corner_def
  have near : dist (f corner) corner < d := by
    refine (dist_pi_lt_iff d_pos).mpr fun i => ?_
    obtain ⟨r, s, rCell, sCell, rFlag, sFlag⟩ := both i
    have rNear := dist_gridPoint_le q base r rCell
    have sNear := dist_gridPoint_le q base s sCell
    have rImage := close (lt_of_le_of_lt rNear fineδ)
    have sImage := close (lt_of_le_of_lt sNear fineδ)
    have rPoint := le_trans (dist_le_pi_dist (gridPoint q r) corner i) rNear
    have sPoint := le_trans (dist_le_pi_dist (gridPoint q s) corner i) sNear
    have rValue := lt_of_le_of_lt (dist_le_pi_dist (f (gridPoint q r)) (f corner) i) rImage
    have sValue := lt_of_le_of_lt (dist_le_pi_dist (f (gridPoint q s)) (f corner) i) sImage
    have rUp := flagFalse r i rFlag
    have sDown := flagTrue s i sFlag
    rw [Subtype.dist_eq, Real.dist_eq, abs_le] at rPoint sPoint
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt] at rValue sValue
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    constructor <;> linarith [rPoint.1, rPoint.2, sPoint.1, sPoint.2, rValue.1, rValue.2,
      sValue.1, sValue.2]
  exact absurd (apart corner) (not_le.mpr near)

/-- Brouwer's theorem for the cube over any finite index type. -/
theorem brouwer_cube_fintype {ι : Type*} [Fintype ι] (f : (ι → I) → (ι → I))
    (continuous : Continuous f) : ∃ x, f x = x := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let g : (Fin (Fintype.card ι) → I) → (Fin (Fintype.card ι) → I) :=
    fun y => fun j => f (fun i => y (e i)) (e.symm j)
  have continuousG : Continuous g :=
    continuous_pi fun j => (continuous_apply (e.symm j)).comp
      (continuous.comp (continuous_pi fun i => continuous_apply (e i)))
  obtain ⟨y, fixed⟩ := brouwer_cube _ g continuousG
  refine ⟨fun i => y (e i), funext fun i => ?_⟩
  have at_i := congrFun fixed (e i)
  simpa [g] using at_i

end Mettapedia.Topology
