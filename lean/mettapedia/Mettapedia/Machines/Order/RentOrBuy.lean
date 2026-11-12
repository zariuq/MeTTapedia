import Mathlib.Tactic

/-!
# Walk or gather: the access-path choice of a lazy ordered read

A read of an ordered store may walk the store's order (each row passed costs
one unit, and the walk can stop at any answer) or gather a secondary index's
rows once (a lump cost; afterwards every answer is at hand). A reader that may
stop early does not know in advance how many answers it will take, so it does
not know which plan is cheaper.

This is the rent-or-buy (ski-rental) problem. The break-even rule walks until
the walk has cost what the gather costs, and then gathers. This file proves:

* `breakEven_le_two_opt`: with the switch at the gather's cost, the read costs
  at most twice the better plan, for every demand;
* `breakEven_posted_le`: with the switch at the index's posted row count `c`
  while the gather really costs `γ * c` (`γ ≥ 1`), at most `(1 + γ)` times;
* `breakEven_le_two_walk`, `breakEven_eq_walk`: never more than twice the walk
  alone, and exactly the walk whenever the walk answers within the price;
* `demand_oblivious`: one switching point serves every demand at once;
* `threshold_lower_bound`, `never_buy_unbounded`: no deterministic switching
  point does better than `2 - 1/p`, and never gathering is unbounded;
* `eagerRule_eq_opt`: a read that takes every answer knows both prices, and
  its branch pays the better one.

Costs are natural numbers in units of one row walked. `walk` is the cost at
which the walk alone would satisfy the demand (at most the rows of the
order's ranges).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Order.RentOrBuy

/-- The read's cost when it walks until `threshold` rows have been passed and
then gathers at cost `gather`: the walk alone if it satisfied the demand within
the threshold, else the rows walked and the gather. -/
def breakEven (walk threshold gather : ℕ) : ℕ :=
  if walk ≤ threshold then walk else threshold + gather

/-- The better of the two plans chosen with hindsight: walk to the answer, or
gather at the start. -/
def opt (walk gather : ℕ) : ℕ := min walk gather

/-- Break-even at the gather's own cost is 2-competitive. -/
theorem breakEven_le_two_opt (walk gather : ℕ) :
    breakEven walk gather gather ≤ 2 * opt walk gather := by
  unfold breakEven opt
  split_ifs with h
  · rw [min_eq_left h]; omega
  · rw [min_eq_right (by omega)]; omega

/-- Break-even at the index's posted row count `c`, when gathering really costs
`γ * c` with `γ ≥ 1`: at most `1 + γ` times the better plan. -/
theorem breakEven_posted_le (walk c γ : ℕ) (hγ : 1 ≤ γ) :
    breakEven walk c (γ * c) ≤ (1 + γ) * opt walk (γ * c) := by
  unfold breakEven opt
  have hc : c ≤ γ * c := Nat.le_mul_of_pos_left c hγ
  split_ifs with h
  · rw [min_eq_left (le_trans h hc)]
    nlinarith
  · have hle : c ≤ min walk (γ * c) := le_min (by omega) hc
    calc c + γ * c = (1 + γ) * c := by ring
      _ ≤ (1 + γ) * min walk (γ * c) := Nat.mul_le_mul_left _ hle

/-- The rule never costs more than twice the walk alone. -/
theorem breakEven_le_two_walk (walk gather : ℕ) :
    breakEven walk gather gather ≤ 2 * walk := by
  unfold breakEven
  split_ifs with h <;> omega

/-- When the walk answers within the price, the rule is the walk itself. -/
theorem breakEven_eq_walk {walk threshold gather : ℕ} (h : walk ≤ threshold) :
    breakEven walk threshold gather = walk := by
  simp [breakEven, h]

/-- One switching point serves every demand: if the walk delivers its `k`-th
answer after `w k` rows, the rule is within twice the better plan for each `k`,
though it never learns `k`. -/
theorem demand_oblivious (w : ℕ → ℕ) (gather : ℕ) :
    ∀ k, breakEven (w k) gather gather ≤ 2 * opt (w k) gather :=
  fun k => breakEven_le_two_opt (w k) gather

/-- No deterministic switching point does better than `2 - 1/p` against a gather
of cost `p ≥ 1`: the adversary stops the read just after the switch. -/
theorem threshold_lower_bound (threshold p : ℕ) (hp : 1 ≤ p) :
    ∃ walk, (2 * p - 1) * opt walk p ≤ p * breakEven walk threshold p := by
  refine ⟨threshold + 1, ?_⟩
  have hb : breakEven (threshold + 1) threshold p = threshold + p := by
    simp [breakEven]
  rw [hb]
  unfold opt
  by_cases h : threshold + 1 ≤ p
  · rw [min_eq_left h]
    obtain ⟨d, rfl⟩ : ∃ d, p = threshold + 1 + d := ⟨p - (threshold + 1), by omega⟩
    have e : 2 * (threshold + 1 + d) - 1 = 2 * threshold + 2 * d + 1 := by omega
    rw [e]
    nlinarith
  · rw [min_eq_right (by omega)]
    have e : (2 * p - 1) * p + p = 2 * p * p := by
      obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
      have : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
      rw [this]; ring
    nlinarith

/-- Never gathering is not competitive: its ratio against the better plan is
unbounded. -/
theorem never_buy_unbounded (p M : ℕ) :
    ∃ walk, M * opt walk p < walk := by
  refine ⟨M * p + 1, ?_⟩
  unfold opt
  have := Nat.mul_le_mul_left M (min_le_right (M * p + 1) p)
  omega

/-- An eager read, which takes every answer, knows both prices before it starts:
the rows `r` of the order's ranges (counted by ranks) and the posted count `c`.
The branch it takes. -/
def eagerRule (r c : ℕ) : ℕ := if c < r then c else r

/-- The eager branch pays exactly the better plan. -/
theorem eagerRule_eq_opt (r c : ℕ) : eagerRule r c = opt r c := by
  unfold eagerRule opt
  split_ifs with h
  · exact (min_eq_right h.le).symm
  · exact (min_eq_left (not_lt.mp h)).symm

end Mettapedia.Machines.Order.RentOrBuy
