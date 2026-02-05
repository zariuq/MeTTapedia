import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Valuation Algebra (Core Operations)

This file provides a minimal **valuation algebra** core, **parametrized** by a
value type `K`.  This makes it compatible with:

* `K = ℝ≥0∞` (classical probabilistic potentials),
* `K = ℝ` (K&S-regraduated plausibilities),
* or any commutative semiring / valuation scale.

* **Valuations** are information objects scoped to a set of variables.
* **Combination** composes information (pointwise multiplication).
* **Marginalization** focuses information (sum over eliminated variables).

The design intentionally stays close to factor-graph / local-computation practice:
valuations are defined on **full configurations**, and scope is metadata.
This avoids heavy dependent restrictions while still supporting exact definitions.

This is the WM-side foundation needed to represent **overlapping evidence** as
factors rather than assuming additivity of evidence counts.
-/

namespace Mettapedia.ProbabilityTheory.BayesianNetworks

open scoped BigOperators ENNReal

/-! ## Full configurations -/

/-- A full configuration assigns a value to each variable. -/
abbrev FullConfig (V : Type*) (β : V → Type*) := ∀ v : V, β v

/-! ## Valuations -/

/-- A valuation over variables `V` with state spaces `β`.

`scope` is the set of variables the valuation depends on (metadata);
`val` is a nonnegative potential on full configurations. -/
structure Valuation (V : Type*) (β : V → Type*) (K : Type*) where
  scope : Finset V
  val : FullConfig V β → K

namespace Valuation

variable {V : Type*} {β : V → Type*} {K : Type*}

/-! ## Combination -/

/-- Combine two valuations by pointwise multiplication; scope is the union. -/
noncomputable def combine (φ ψ : Valuation V β K) [Mul K] : Valuation V β K := by
  classical
  exact
    { scope := φ.scope ∪ ψ.scope
      val := fun x => φ.val x * ψ.val x }

/-! ## Marginalization -/

/-- Agreement of two full configurations on a variable set `T`. -/
def agreeOn (T : Finset V) (x xT : FullConfig V β) : Prop :=
  ∀ v, v ∈ T → x v = xT v

/-- Finite enumeration of all full configurations (when finite). -/
noncomputable def allConfigs (V : Type*) (β : V → Type*) [Fintype V]
    [∀ v, Fintype (β v)] : Finset (FullConfig V β) := by
  classical
  exact Fintype.piFinset (fun v : V => (Finset.univ : Finset (β v)))

/-- Marginalize a valuation to scope `T` by summing over all full configurations
that agree with the partial assignment on `T`. -/
noncomputable def marginalize (φ : Valuation V β K) (T : Finset V)
    [Fintype V] [∀ v, Fintype (β v)] [AddCommMonoid K] : Valuation V β K := by
  classical
  exact
    { scope := T
      val := fun xT =>
        (allConfigs V β).sum (fun x =>
          if agreeOn (β := β) T x xT then φ.val x else 0) }

/-! ### Common specializations -/

/-- Probabilistic potentials (classical BN/FG). -/
abbrev ProbValuation (V : Type*) (β : V → Type*) := Valuation V β ℝ≥0∞

/-- K&S-regraduated potentials (plausibility scale on ℝ). -/
abbrev KSValuation (V : Type*) (β : V → Type*) := Valuation V β ℝ

end Valuation

end Mettapedia.ProbabilityTheory.BayesianNetworks
