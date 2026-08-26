import Mathlib.SetTheory.Cardinal.Arithmetic
import Mettapedia.Cybernetics.HierarchicalComplexity.Finite

/-!
# Infinite branching and the boundary of the finite `phi` law

The finite Commons--Pekker theorem says that the minimum number of simple
actions at natural-number order `n` is `2^n`.  It does not state a transfinite
cardinal-exponentiation law.  The countably branching limit chain below makes
that distinction formal: its ordinal rank is `omega`, its simple-leaf cardinal
is only `aleph0`, and therefore it is strictly smaller than `2^aleph0`.

This is an extension and negative control developed here, not a claim made by
Commons and Pekker.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

open LimitCanary

namespace InfiniteCanary

/-- The binary finite-order tower has exactly `2^n` simple leaves before
taking the natural-cardinality readout. -/
theorem simpleLeafCardinal_finiteTower (n : Nat) :
    Action.simpleLeafCardinal (finiteTower n) = (2 : Cardinal) ^ n := by
  letI : _root_.Finite (Action.SimpleLeaves (finiteTower n)) :=
    Action.finite_simpleLeaves (finiteTower n)
      (Finite.Phi.finitelyBranching_finiteTower n)
  rw [Action.simpleLeafCardinal]
  rw [← Nat.cast_card]
  simp only [Finite.Phi.natCard_simpleLeaves_finiteTower, Nat.cast_pow,
    Nat.cast_ofNat]

/-- The limit chain is not finitely branching; hence the finite `phi` theorem
cannot be applied to it. -/
theorem limitChain_not_finitelyBranching :
    ¬ Action.FinitelyBranching limitChain := by
  intro finite
  have below := Action.rank_lt_omega0_of_finitelyBranching limitChain finite
  rw [rank_limitChain] at below
  exact (lt_irrefl Ordinal.omega0) below

/-- The countable family of finite towers has exactly countably many simple
leaves. -/
theorem simpleLeafCardinal_limitChain :
    Action.simpleLeafCardinal limitChain = Cardinal.aleph0 := by
  rw [limitChain, Action.simpleLeafCardinal_compound]
  simp_rw [simpleLeafCardinal_finiteTower]
  rw [Cardinal.sum_pow_eq_max_aleph0]
  · simp
  · exact two_ne_zero

/-- Naively replacing the finite exponent in `phi n = 2^n` by cardinal
exponentiation at the limit gives the wrong answer for this chain. -/
theorem simpleLeafCardinal_limitChain_lt_two_power_aleph0 :
    Action.simpleLeafCardinal limitChain <
      (2 : Cardinal) ^ Cardinal.aleph0 := by
  rw [simpleLeafCardinal_limitChain]
  exact Cardinal.cantor Cardinal.aleph0

end InfiniteCanary

end Mettapedia.Cybernetics.HierarchicalComplexity

#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.InfiniteCanary.simpleLeafCardinal_limitChain
#print axioms Mettapedia.Cybernetics.HierarchicalComplexity.InfiniteCanary.simpleLeafCardinal_limitChain_lt_two_power_aleph0
