import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# No-Go: Chain Coverage Collapse

This module formalizes the **chain coverage collapse** no-go theorem for
certified PLN chaining:

If each of n prediction steps has per-step coverage probability at most `1 - α`
(i.e., miss probability at least `α`), then the joint coverage—the probability
that all n steps succeed simultaneously—decays exponentially:

    joint_coverage ≤ (1 - α)^n

In particular, for any fixed `α > 0`, the joint coverage tends to 0 as `n → ∞`,
regardless of how accurate individual steps are.

**Design implication**: certified per-step guarantees cannot be composed into
chain-length-independent certificates. Adaptive truncation is necessary.

## References

This is a no-go theorem for the WM-PLN certified chaining system.
-/

namespace Mettapedia.Logic.PLNCoverageCollapseNoGo

open scoped BigOperators

/-! ## Main no-go theorem -/

/-- **Coverage collapse**: if every per-step coverage probability is at most `1 - α`,
then the joint coverage (product of all per-step probabilities) is at most `(1 - α)^n`.

This formalizes the key limitation of certified chain composition:
individual step guarantees compound multiplicatively, causing exponential decay. -/
theorem coverage_collapse (n : ℕ) (α : ℝ) (_hα0 : 0 ≤ α) (_hα1 : α ≤ 1)
    (ps : Fin n → ℝ) (hnn : ∀ i, 0 ≤ ps i) (hub : ∀ i, ps i ≤ 1 - α) :
    ∏ i, ps i ≤ (1 - α) ^ n := by
  calc ∏ i : Fin n, ps i
      ≤ ∏ _i : Fin n, (1 - α) := by
          apply Finset.prod_le_prod
          · intro i _; exact hnn i
          · intro i _; exact hub i
    _ = (1 - α) ^ n := by simp [Finset.prod_const]

/-! ## Corollary: exponential decay to zero -/

/-- **Exponential decay**: for any positive miss rate `α ∈ (0, 1]`, the joint coverage
`(1 - α)^n` tends to 0 as the chain length `n → ∞`.

This is the fundamental reason that long certified chains cannot maintain coverage. -/
theorem coverage_collapse_decay (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) :
    Filter.Tendsto (fun n => (1 - α) ^ n) Filter.atTop (nhds 0) := by
  apply tendsto_pow_atTop_nhds_zero_of_lt_one
  · linarith
  · linarith

/-! ## Quantitative corollary: explicit ε-chain-length bound -/

/-- For any desired joint coverage `ε > 0` and per-step miss rate `α ∈ (0, 1)`,
the maximum chain length `n` such that `(1 - α)^n ≥ ε` is bounded:
specifically `(1 - α)^n < ε` for all sufficiently large `n`. -/
theorem coverage_below_threshold (α ε : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (1 - α) ^ n < ε := by
  have htend : Filter.Tendsto (fun n => (1 - α) ^ n) Filter.atTop (nhds 0) :=
    coverage_collapse_decay α hα0 (le_of_lt hα1)
  have hev : ∀ᶠ n in Filter.atTop, (1 - α) ^ n ∈ Set.Iio ε :=
    htend.eventually (Iio_mem_nhds hε)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  exact ⟨N, fun n hn => Set.mem_Iio.mp (hN n hn)⟩

/-! ## Tight example: per-step conformal prediction -/

/-- **Tightness**: the bound `(1 - α)^n` is achieved when every per-step
coverage equals exactly `1 - α`.  The joint coverage is then precisely `(1 - α)^n`,
showing the bound is exact (not merely conservative). -/
theorem coverage_collapse_tight (n : ℕ) (α : ℝ) :
    ∏ _i : Fin n, (1 - α) = (1 - α) ^ n := by
  simp [Finset.prod_const]

end Mettapedia.Logic.PLNCoverageCollapseNoGo
