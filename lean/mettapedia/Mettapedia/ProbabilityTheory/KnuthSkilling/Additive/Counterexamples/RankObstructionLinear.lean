import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples

open Classical KnuthSkillingAlgebra

/-!
# A reusable obstruction to `KSSeparation` (rank into an ordered additive monoid)

`RankObstruction.lean` records a common reason `KSSeparation` fails in noncommutative models:
there is a “rank” coordinate that scales under `iterate_op`, and distinct elements can share the
same rank. Then the `KSSeparation.separation` sandwich forces an impossible strict inequality.

This variant packages the same argument with a more general rank codomain `β`.  We avoid relying
on any bundled “LinearOrdered…Monoid” typeclasses (which have been removed upstream in Mathlib);
instead we require exactly what the proof uses:

- an additive monoid structure on `β` with a preorder, and
- strict monotonicity of left addition (`AddLeftStrictMono β`) so `nsmul` is strictly monotone for
  positive elements.

This is still not a full impossibility theorem for K&S: it only rules out models admitting such a
rank structure.
-/

variable {α : Type*} [KnuthSkillingAlgebra α]

structure RankDataLinear (β : Type*) [AddCommMonoid β] [PartialOrder β] [AddLeftStrictMono β] where
  rk : α → β
  rk_le_of_le : ∀ {x y : α}, x ≤ y → rk x ≤ rk y
  rk_iterate : ∀ x n, rk (iterate_op x n) = n • rk x
  rk_pos_of_ident_lt : ∀ {x : α}, ident < x → 0 < rk x

theorem not_KSSeparation_of_same_rank_linear
    {β : Type*} [AddCommMonoid β] [PartialOrder β] [AddLeftStrictMono β]
    (R : RankDataLinear (α := α) β)
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

  -- Expand ranks using the iterate scaling law and the equal-rank hypothesis.
  have h_rk_xm : R.rk (iterate_op x m) = m • R.rk x := R.rk_iterate x m
  have h_rk_an : R.rk (iterate_op a n) = n • R.rk a := R.rk_iterate a n
  have h_rk_ym : R.rk (iterate_op y m) = m • R.rk y := R.rk_iterate y m

  have h_mr_le_nr : m • R.rk x ≤ n • R.rk a := by
    simpa [h_rk_xm, h_rk_an] using h_rk_xm_le_an
  have h_nr_le_mr : n • R.rk a ≤ m • R.rk y := by
    simpa [h_rk_an, h_rk_ym] using h_rk_an_le_ym

  -- Reduce to `m•r ≤ n•r` and `n•r ≤ m•r` for a single `r`, hence equality.
  have h_mr_le_nr' : m • R.rk a ≤ n • R.rk a := by
    simpa [hax_rk] using h_mr_le_nr
  have h_nr_le_mr' : n • R.rk a ≤ m • R.rk a := by
    simpa [hax_rk, hxy_rk] using h_nr_le_mr

  have h_eq : m • R.rk a = n • R.rk a := le_antisymm h_mr_le_nr' h_nr_le_mr'

  have hr_pos : 0 < R.rk a := R.rk_pos_of_ident_lt ha_pos

  -- Since `nsmul` is strictly monotone for positive elements, equality forces `m = n`.
  have hm_eq_hn : m = n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hmn | hnm
    · have hlt : m • R.rk a < n • R.rk a := nsmul_lt_nsmul_left hr_pos hmn
      have hle : n • R.rk a ≤ m • R.rk a := le_of_eq h_eq.symm
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
    · have hlt : n • R.rk a < m • R.rk a := nsmul_lt_nsmul_left hr_pos hnm
      have hle : m • R.rk a ≤ n • R.rk a := le_of_eq h_eq
      exact lt_irrefl _ (lt_of_lt_of_le hlt hle)

  -- With `m = n`, the sandwich gives `x^m < a^m`, contradicting strict monotonicity in the base
  -- element since `a < x` implies `a^m < x^m` for `m>0`.
  have ham_lt : iterate_op a m < iterate_op x m :=
    KnuthSkillingAlgebra.iterate_op_strictMono_base m hm_pos a x hax
  have hxm_lt' : iterate_op x m < iterate_op a m := by simpa [hm_eq_hn] using hxm_lt
  exact lt_irrefl (iterate_op a m) (lt_trans ham_lt hxm_lt')

/-!
## Corollary: `KSSeparation` forbids rank-collisions along a chain

If a candidate model admits a monotone additive “rank” into an ordered additive monoid `β`, then
any triple `a < x < y` of positive elements sharing the same rank would contradict
`KSSeparation.separation`.

This is a convenient “obstruction checklist” lemma when hunting for noncommutative models:
many natural noncommutative constructions (shortlex words, semidirect products, …) have such a
rank coordinate, and this corollary explains why they systematically fail `KSSeparation`.
-/
theorem KSSeparation.no_same_rank_chain_linear
    {β : Type*} [AddCommMonoid β] [PartialOrder β] [AddLeftStrictMono β]
    [KSSeparation α] (R : RankDataLinear (α := α) β) :
    ¬ (∃ a x y : α,
        ident < a ∧ ident < x ∧ ident < y ∧ a < x ∧ x < y ∧
        R.rk a = R.rk x ∧ R.rk x = R.rk y) := by
  intro hChain
  have : ¬ KSSeparation α := not_KSSeparation_of_same_rank_linear (α := α) (R := R) hChain
  exact this inferInstance

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Counterexamples
