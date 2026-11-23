import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Optimal collection headroom in the stationary scan-work model

If the measured cost of a collection is stable and allocations arrive at
a fixed rate, the collection cost per unit time has the form `work / h`,
where `h` is fresh headroom, not live size. Its memory charge is `price * h`.
This is the model of Kirisame, Shenoy and Panchekha (OOPSLA 2022).
The exact loss formula also compares policies without derivatives.

This does not select a runtime default. Root inventory counts toward scan
work; integer rounding, phase changes, promotion, pause limits, and safe
points need separate evidence. A cap here bounds additional headroom only.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CollectionHeadroom

noncomputable def cost (price work extra : ℝ) : ℝ := price * extra + work / extra

noncomputable def optimum (price work : ℝ) : ℝ := √(work / price)

theorem optimum_pos {price work : ℝ} (hp : 0 < price) (hw : 0 < work) :
    0 < optimum price work := by
  unfold optimum
  exact Real.sqrt_pos.2 (div_pos hw hp)

theorem balance {price work : ℝ} (hp : 0 < price) (hw : 0 ≤ work) :
    work = price * optimum price work ^ 2 := by
  rw [optimum, Real.sq_sqrt (div_nonneg hw hp.le)]
  field_simp

/-- The quantity lost by choosing another feasible headroom around a
balanced point. No stationary-rate assumption is hidden in the algebra. -/
theorem loss_at_balanced {price work extra best : ℝ}
    (he : 0 < extra) (hb : 0 < best) (balanced : work = price * best ^ 2) :
    cost price work extra - cost price work best = price * (extra - best) ^ 2 / extra := by
  have atBest : price * best ^ 2 / best = price * best := by
    apply (div_eq_iff hb.ne').mpr
    ring
  rw [balanced]
  simp only [cost, atBest]
  field_simp [he.ne']
  ring

theorem optimum_unique {price work extra : ℝ} (hp : 0 < price) (hw : 0 < work)
    (he : 0 < extra) :
    cost price work (optimum price work) ≤ cost price work extra ∧
      (cost price work extra = cost price work (optimum price work) ↔
        extra = optimum price work) := by
  have gap := loss_at_balanced he (optimum_pos hp hw) (balance hp hw.le)
  constructor
  · rw [← sub_nonneg, gap]
    positivity
  · constructor
    · intro equal
      have zero : price * (extra - optimum price work) ^ 2 / extra = 0 := by
        rw [← gap, equal, sub_self]
      have square := (mul_eq_zero.mp ((div_eq_zero_iff.mp zero).resolve_right he.ne')).resolve_left hp.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp square)
    · intro same
      rw [same]

theorem difference {price work x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    cost price work x - cost price work y =
      (y - x) * (work - price * x * y) / (x * y) := by
  unfold cost
  field_simp [hx.ne', hy.ne']
  ring

private theorem cost_decreasing_below_optimum {price work x y : ℝ}
    (hp : 0 < price) (hw : 0 < work) (hx : 0 < x) (order : x < y)
    (below : y ≤ optimum price work) : cost price work y < cost price work x := by
  have hy := hx.trans order
  have prod : x * y < optimum price work ^ 2 :=
    (mul_lt_mul_of_pos_right order hy).trans_le (by
      rw [sq]
      exact mul_le_mul below below hy.le (optimum_pos hp hw).le)
  have gain : 0 < work - price * x * y := by
    rw [balance hp hw.le, mul_assoc]
    exact sub_pos.mpr (mul_lt_mul_of_pos_left prod hp)
  rw [← sub_pos, difference hx hy]
  exact div_pos (mul_pos (sub_pos.mpr order) gain) (mul_pos hx hy)

/-- A positive hard cap clips the unconstrained optimum, with strict loss
for every other feasible choice. -/
theorem capped_optimum {price work cap extra : ℝ}
    (hp : 0 < price) (hw : 0 < work) (he : 0 < extra) (within : extra ≤ cap) :
    let best := min cap (optimum price work)
    0 < best ∧ best ≤ cap ∧ cost price work best ≤ cost price work extra ∧
      (cost price work extra = cost price work best ↔ extra = best) := by
  have hcap := lt_of_lt_of_le he within
  have hopt := optimum_pos hp hw
  by_cases small : cap ≤ optimum price work
  · simp only [min_eq_left small]
    refine ⟨hcap, le_rfl, ?_, ?_⟩
    · by_cases equal : extra = cap
      · rw [equal]
      · exact (cost_decreasing_below_optimum hp hw he (lt_of_le_of_ne within equal) small).le
    · refine ⟨?_, fun same => by rw [same]⟩
      intro equal
      by_contra different
      exact (cost_decreasing_below_optimum hp hw he
        (lt_of_le_of_ne within different) small).ne equal.symm
  · have large := le_of_not_ge small
    simp only [min_eq_right large]
    exact ⟨hopt, large, (optimum_unique hp hw he).1, (optimum_unique hp hw he).2⟩

/-- With unit memory price, no fixed proportional headroom rule has a
uniform approximation factor over positive stationary work coefficients.
This compares the uncapped regime only. -/
theorem proportional_loss_unbounded (multiple factor : ℝ)
    (hm : 0 < multiple) (hf : 0 < factor) :
    ∃ work : ℝ, 0 < work ∧
      factor * cost 1 work (optimum 1 work) < cost 1 work (multiple * work) := by
  let root := 2 * factor / multiple
  have rootPos : 0 < root := div_pos (mul_pos (by norm_num) hf) hm
  have workPos : 0 < root ^ 2 := pow_pos rootPos _
  have best : optimum 1 (root ^ 2) = root := by
    simpa only [optimum, div_one] using Real.sqrt_sq rootPos.le
  have optimalCost : cost 1 (root ^ 2) root = 2 * root := by
    unfold cost
    field_simp [rootPos.ne']
    ring
  have proportionCost : cost 1 (root ^ 2) (multiple * root ^ 2) =
      multiple * root ^ 2 + 1 / multiple := by
    unfold cost
    rw [one_mul]
    congr 1
    field_simp [hm.ne', workPos.ne']
  have scales : factor * (2 * root) = multiple * root ^ 2 := by
    dsimp [root]
    field_simp [hm.ne']
  refine ⟨root ^ 2, workPos, ?_⟩
  rw [best, optimalCost, proportionCost, scales]
  exact lt_add_of_pos_right _ (one_div_pos.mpr hm)

section SharedBudget

variable {Region : Type*}

noncomputable def rootSum (regions : Finset Region) (work : Region → ℝ) : ℝ :=
  ∑ r ∈ regions, √(work r)

/-- All regions use one price: fresh space is apportioned by square roots
of their measured scan-work coefficients. -/
noncomputable def apportioned (regions : Finset Region) (work : Region → ℝ)
    (budget : ℝ) (r : Region) : ℝ :=
  budget * √(work r) / rootSum regions work

theorem apportion_optimal (regions : Finset Region) (work actual : Region → ℝ)
    (budget : ℝ) (hb : 0 < budget) (nonempty : regions.Nonempty)
    (hw : ∀ r ∈ regions, 0 < work r) (ha : ∀ r ∈ regions, 0 < actual r)
    (sameBudget : ∑ r ∈ regions, actual r = budget) :
    (∀ r ∈ regions, 0 < apportioned regions work budget r) ∧
      (∑ r ∈ regions, apportioned regions work budget r) = budget ∧
      (∑ r ∈ regions, work r / apportioned regions work budget r) ≤
        ∑ r ∈ regions, work r / actual r := by
  have totalPos : 0 < rootSum regions work := by
    unfold rootSum
    exact Finset.sum_pos (fun r hr => Real.sqrt_pos.2 (hw r hr)) nonempty
  let price := (rootSum regions work / budget) ^ 2
  have hp : 0 < price := by dsimp [price]; positivity
  have positive : ∀ r ∈ regions, 0 < apportioned regions work budget r := by
    intro r hr
    exact div_pos (mul_pos hb (Real.sqrt_pos.2 (hw r hr))) totalPos
  have accounted : (∑ r ∈ regions, apportioned regions work budget r) = budget := by
    simp only [apportioned, ← Finset.sum_div, ← Finset.mul_sum]
    change budget * rootSum regions work / rootSum regions work = budget
    field_simp [totalPos.ne']
  have balanced (r : Region) (hr : r ∈ regions) :
      work r = price * apportioned regions work budget r ^ 2 := by
    dsimp [price, apportioned]
    rw [div_pow, div_pow, mul_pow, Real.sq_sqrt (hw r hr).le]
    field_simp [hb.ne', totalPos.ne']
  have regionsBetter : (∑ r ∈ regions, cost price (work r) (apportioned regions work budget r)) ≤
      ∑ r ∈ regions, cost price (work r) (actual r) := by
    apply Finset.sum_le_sum
    intro r hr
    rw [← sub_nonneg, loss_at_balanced (ha r hr) (positive r hr) (balanced r hr)]
    exact div_nonneg (mul_nonneg hp.le (sq_nonneg _)) (ha r hr).le
  simp only [cost, Finset.sum_add_distrib, ← Finset.mul_sum, accounted, sameBudget] at regionsBetter
  exact ⟨positive, accounted, le_of_add_le_add_left regionsBetter⟩

end SharedBudget

namespace Controls

theorem excessive_headroom_costs_more :
    cost 1 4 (optimum 1 4) < cost 1 4 4 := by
  norm_num [cost, optimum]

/-- When affordability binds, using the whole permitted cap is better
than retrying collection with less headroom. -/
theorem cap_can_bind : cost 1 4 1 < cost 1 4 (1 / 2) := by norm_num [cost]

end Controls
end Mettapedia.Machines.CollectionHeadroom
