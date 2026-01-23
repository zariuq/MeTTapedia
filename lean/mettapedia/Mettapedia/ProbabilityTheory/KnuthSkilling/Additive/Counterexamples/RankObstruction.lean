import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples

open Classical KnuthSkillingAlgebra

/-!
# A reusable obstruction to `KSSeparation`

This file factors the core pattern used in `SemidirectNoSeparation.lean`:

If the order admits a “rank” map `rk : α → ℕ` that:
- is monotone w.r.t. `≤`,
- scales under `iterate_op` as `rk (x^n) = n * rk x`,
- is positive above `ident`,

then *any* triple `a < x < y` with the same rank forces `¬ KSSeparation α`.

This is not a full impossibility proof for K&S (it only rules out a broad and common family of
noncommutative constructions that come with such a rank), but it is a clean way to keep search
efforts on track: if a proposed countermodel carries this kind of rank, it cannot satisfy
`KSSeparation`.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

structure RankData (α : Type*) [KnuthSkillingAlgebra α] where
  rk : α → ℕ
  rk_le_of_le : ∀ {x y : α}, x ≤ y → rk x ≤ rk y
  rk_iterate : ∀ x n, rk (iterate_op x n) = n * rk x
  rk_pos_of_ident_lt : ∀ {x : α}, ident < x → 0 < rk x

theorem not_KSSeparation_of_same_rank
    (R : RankData α)
    (hChain :
      ∃ a x y : α,
        ident < a ∧ ident < x ∧ ident < y ∧ a < x ∧ x < y ∧
        R.rk a = R.rk x ∧ R.rk x = R.rk y) :
    ¬ KSSeparation α := by
  intro hSep
  rcases hChain with ⟨a, x, y, ha_pos, hx_pos, hy_pos, hax, hxy, hax_rk, hxy_rk⟩
  rcases hSep.separation (a := a) (x := x) (y := y) ha_pos hx_pos hy_pos hxy with
    ⟨n, m, hm_pos, hxm_lt, han_le⟩

  -- Compare `rk` across the sandwich `x^m < a^n ≤ y^m`.
  have h_rk_xm_le_an : R.rk (iterate_op x m) ≤ R.rk (iterate_op a n) :=
    R.rk_le_of_le (show iterate_op x m ≤ iterate_op a n from (le_of_lt hxm_lt))
  have h_rk_an_le_ym : R.rk (iterate_op a n) ≤ R.rk (iterate_op y m) :=
    R.rk_le_of_le han_le

  -- Expand the ranks using the iterate scaling law and the equal-rank hypothesis.
  have h_rk_xm : R.rk (iterate_op x m) = m * R.rk x := R.rk_iterate x m
  have h_rk_an : R.rk (iterate_op a n) = n * R.rk a := R.rk_iterate a n
  have h_rk_ym : R.rk (iterate_op y m) = m * R.rk y := R.rk_iterate y m

  have h_mr_le_nr : m * R.rk x ≤ n * R.rk a := by
    simpa [h_rk_xm, h_rk_an] using h_rk_xm_le_an
  have h_nr_le_mr : n * R.rk a ≤ m * R.rk y := by
    simpa [h_rk_an, h_rk_ym] using h_rk_an_le_ym

  -- Reduce to `m * r ≤ n * r` and `n * r ≤ m * r` for a single `r`, hence equality.
  have h_mr_le_nr' : m * R.rk a ≤ n * R.rk a := by
    simpa [hax_rk] using h_mr_le_nr
  have h_nr_le_mr' : n * R.rk a ≤ m * R.rk a := by
    simpa [hax_rk, hxy_rk] using h_nr_le_mr

  have h_eq : m * R.rk a = n * R.rk a := le_antisymm h_mr_le_nr' h_nr_le_mr'

  have hr_pos : 0 < R.rk a := R.rk_pos_of_ident_lt ha_pos
  have hm_eq_hn : m = n := by
    -- Cancel the positive factor `rk a`.
    exact Nat.mul_right_cancel hr_pos h_eq

  -- With `m = n`, the sandwich gives `x^m < a^m`, contradicting strict monotonicity in the base
  -- element since `a < x` implies `a^m < x^m` for `m>0`.
  have ham_lt : iterate_op a m < iterate_op x m :=
    KnuthSkillingAlgebra.iterate_op_strictMono_base m hm_pos a x hax
  have hxm_lt' : iterate_op x m < iterate_op a m := by simpa [hm_eq_hn] using hxm_lt
  exact lt_irrefl (iterate_op a m) (lt_trans ham_lt hxm_lt')

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples
