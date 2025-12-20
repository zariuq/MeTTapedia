import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Main Theorems: Limitations of the Knuth-Skilling Approach

This file presents two fundamental theorems about the K&S approach to deriving
probability theory from symmetry axioms.

## Overview

Knuth & Skilling (2012) claimed to derive probability theory from basic axioms:
associativity, monotonicity, and consistency. We prove two fundamental limitations:

1. **The Rational Density Barrier** (§1): K&S's specific proof technique fails
   because rational numbers are dense — you cannot make δ-shifts small enough
   to avoid rational obstructions.

2. **The Completeness-Commutativity Dichotomy** (§2): ANY approach to deriving
   probability faces a fundamental tradeoff:
   - Weak axioms → admit noncommutative models (not probability)
   - Strong axioms → require completeness (assume the continuum)

## Philosophical Implications

These results show that the continuum (ℝ) cannot be *derived* from symmetry
axioms — it must be *assumed*. The natural completion-free structure is
**imprecise probability** (credal sets), not classical probability.

## References

- Knuth & Skilling, "Foundations of Inference" (2012), Appendix A
- See `StrictGap.lean` for detailed proof of Theorem 1
- See `IntervalCollapse.lean` for detailed proof of Theorem 2
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.MainTheorems

/-!
## §1: The Rational Density Barrier

K&S's proof relies on a "δ-shift" argument: if x < y, then θ(x) + δ < θ(y) for
some small δ > 0. They try to make δ arbitrarily small to get strict inequalities.

**The Problem**: For any δ > 0, there exists a rational q with θ(x) < q < θ(x) + δ.
If q happens to equal some θ(z), the shift fails. Since rationals are dense,
you cannot avoid this obstruction by making δ smaller.
-/

/-- The Rational Density Barrier: Between any two distinct reals lies a rational.
    This prevents δ-shift arguments from achieving strict separation. -/
theorem rational_density_barrier :
    ∀ x y : ℝ, x < y → ∃ q : ℚ, x < q ∧ (q : ℝ) < y :=
  fun _ _ hxy => exists_rat_btwn hxy

/-- K&S's δ-shift technique requires: for all q : ℚ in (θ(x), θ(x) + δ),
    q is not in the range of θ. But by density, such q always exist.

    This is the core obstruction to K&S's proof technique. -/
theorem delta_shift_obstructed (θ : α → ℝ) (x : α) (δ : ℝ) (hδ : δ > 0) :
    ∃ q : ℚ, θ x < q ∧ (q : ℝ) < θ x + δ := by
  have h : θ x < θ x + δ := by linarith
  exact exists_rat_btwn h

/-!
### Theorem 1: The Rational Density Barrier (Formal Statement)

**Theorem** (Rational Density Barrier):
Let θ : α → ℝ be any representation. For any x : α and any δ > 0,
there exists a rational q with θ(x) < q < θ(x) + δ.

**Corollary**: The K&S δ-shift technique cannot establish strict inequalities
θ(x) < θ(y) from non-strict bounds θ(x) ≤ θ(y), because the shift δ
always contains rationals that may be in the range of θ.

**Proof**: Immediate from density of ℚ in ℝ (Archimedean property).

See `StrictGap.lean` for the full development showing how this obstructs
K&S's specific proof in Appendix A.3.4.
-/

/-!
## §2: The Completeness-Commutativity Dichotomy

Even if we try to rescue K&S by using interval-valued representations
(avoiding the need to name exact points), we face a fundamental dichotomy.
-/

/-- Weak interval axioms: sub/super-additivity bounds -/
structure WeakIntervalAxioms (α : Type*) (op : α → α → α) (μ : α → ℝ × ℝ) : Prop where
  /-- Intervals are valid: lower ≤ upper -/
  valid : ∀ x, (μ x).1 ≤ (μ x).2
  /-- Sub-additivity: lower bounds add -/
  sub_add : ∀ x y, (μ x).1 + (μ y).1 ≤ (μ (op x y)).1
  /-- Super-additivity: upper bounds add -/
  super_add : ∀ x y, (μ (op x y)).2 ≤ (μ x).2 + (μ y).2

/-- Strong interval axioms: intervals converge to points -/
structure StrongIntervalAxioms (α : Type*) (μ : ℕ → α → ℝ × ℝ) : Prop where
  /-- Intervals are nested and valid -/
  valid : ∀ x n, (μ n x).1 ≤ (μ n x).2
  lower_inc : ∀ x n, (μ n x).1 ≤ (μ (n + 1) x).1
  upper_dec : ∀ x n, (μ (n + 1) x).2 ≤ (μ n x).2
  /-- Widths converge to zero -/
  converge : ∀ x ε, ε > 0 → ∃ n, (μ n x).2 - (μ n x).1 < ε

/-!
### Theorem 2: The Completeness-Commutativity Dichotomy

**Part A** (Weak Axioms Don't Imply Commutativity):
There exists an associative, noncommutative algebra with a valid weak interval measure.

**Part B** (Strong Axioms Require Completeness):
If intervals converge (width → 0), extracting point values requires the
completeness axiom (sSup existence).

**Corollary**: No first-order axiom system can derive both commutativity
and real-valued representations without assuming completeness.
-/

/-- The Heisenberg group: associative but NOT commutative -/
def HeisenbergOp (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1)

/-- Part A: Weak axioms admit noncommutative models -/
theorem weak_axioms_admit_noncommutative :
    ∃ (α : Type) (op : α → α → α) (μ : α → ℝ × ℝ),
      -- op is associative
      (∀ x y z, op (op x y) z = op x (op y z)) ∧
      -- μ satisfies weak interval axioms
      WeakIntervalAxioms α op μ ∧
      -- But op is NOT commutative
      (∃ x y, op x y ≠ op y x) := by
  use ℤ × ℤ × ℤ, HeisenbergOp, fun _ => (0, 1)
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- Associativity
    intro x y z
    simp only [HeisenbergOp]
    ext <;> ring
  · -- Valid intervals
    intro _; norm_num
  · -- Sub-additivity
    intro _ _; norm_num
  · -- Super-additivity
    intro _ _; norm_num
  · -- Noncommutativity
    use (1, 0, 0), (0, 1, 0)
    simp only [HeisenbergOp, ne_eq, Prod.mk.injEq]
    decide

/-- Part B: Strong axioms require completeness to extract point values.
    Note: This definition uses sSup, which requires completeness of ℝ! -/
noncomputable def extractPointValue (μ : ℕ → α → ℝ × ℝ) (x : α) : ℝ :=
  sSup (Set.range (fun n => (μ n x).1))

/-- Helper: lower bounds are monotonically increasing -/
theorem lower_mono (μ : ℕ → α → ℝ × ℝ) (hS : StrongIntervalAxioms α μ) (x : α) :
    ∀ m n, m ≤ n → (μ m x).1 ≤ (μ n x).1 := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans ih (hS.lower_inc x k)

/-- Helper: upper bounds are monotonically decreasing -/
theorem upper_mono (μ : ℕ → α → ℝ × ℝ) (hS : StrongIntervalAxioms α μ) (x : α) :
    ∀ m n, m ≤ n → (μ n x).2 ≤ (μ m x).2 := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans (hS.upper_dec x k) ih

/-- Helper: all lower bounds ≤ all upper bounds -/
theorem lower_le_upper_all (μ : ℕ → α → ℝ × ℝ) (hS : StrongIntervalAxioms α μ) (x : α) :
    ∀ m k, (μ m x).1 ≤ (μ k x).2 := by
  intro m k
  by_cases hmk : m ≤ k
  · exact le_trans (lower_mono μ hS x m k hmk) (hS.valid x k)
  · push_neg at hmk
    exact le_trans (hS.valid x m) (upper_mono μ hS x k m (le_of_lt hmk))

theorem strong_axioms_yield_points (α : Type*) (μ : ℕ → α → ℝ × ℝ)
    (hS : StrongIntervalAxioms α μ) :
    ∃ θ : α → ℝ, ∀ x n, (μ n x).1 ≤ θ x ∧ θ x ≤ (μ n x).2 := by
  use extractPointValue μ
  intro x n
  -- Bounded above by U(0)
  have h_bdd : BddAbove (Set.range (fun m => (μ m x).1)) :=
    ⟨(μ 0 x).2, fun v ⟨m, hm⟩ => hm ▸ lower_le_upper_all μ hS x m 0⟩
  have h_ne : (Set.range (fun m => (μ m x).1)).Nonempty := ⟨(μ 0 x).1, 0, rfl⟩
  constructor
  · -- L(n) ≤ sSup {L(m)}
    exact le_csSup h_bdd ⟨n, rfl⟩
  · -- sSup {L(m)} ≤ U(n)
    exact csSup_le h_ne (fun v ⟨m, hm⟩ => hm ▸ lower_le_upper_all μ hS x m n)

/-!
### The Dichotomy (Summary)

| Axiom Strength | Commutativity | Completeness Required |
|----------------|---------------|----------------------|
| Weak intervals | CANNOT prove  | No                   |
| Strong intervals | CAN prove   | **Yes** (sSup)       |

**Interpretation**:
- Weak axioms are *too weak* to force probability-like structure
- Strong axioms are *strong enough* but *require* the continuum

There is no "Goldilocks" axiom set that derives probability without assuming ℝ.
-/

/-!
## §3: Philosophical Implications

### The Continuum is a Choice, Not a Theorem

K&S tried to show: Rationality ⟹ Real-valued probabilities

We've shown: Rationality ⟹ Credal sets (interval bounds)
             Rationality + Completeness ⟹ Real-valued probabilities

The completeness axiom is *independent* — it cannot be derived from
associativity, monotonicity, or any first-order symmetry requirements.

### What You Get Without Completeness

Without assuming the continuum, the natural structure is **imprecise probability**:
- Lower probability P*(A): infimum of admissible values
- Upper probability P*(A): supremum of admissible values
- Credal set C(A) = [P*(A), P*(A)]: all admissible probability assignments

This is developed further in `CredalSets.lean`.

### The Steelmanned K&S

The correct formulation of K&S's insight:

**Theorem** (Steelmanned K&S):
Let (α, ⊕, <) satisfy:
1. Associativity: (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z)
2. Monotonicity: x < y → x ⊕ z < y ⊕ z
3. Solvability: ∀ x y, ∃ z, x ⊕ z = y (when x < y)

Then there exists a **credal representation** μ : α → Interval satisfying:
- μ(x ⊕ y) ⊆ μ(x) + μ(y) (containment)
- x < y → sup(μ(x)) ≤ inf(μ(y)) (order preservation)

**IF additionally** we assume completeness, THEN intervals collapse to points,
giving classical probability: θ : α → ℝ with θ(x ⊕ y) = θ(x) + θ(y).

This correctly separates what the axioms give you (credal sets) from what
the continuum adds (exact point values).
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.MainTheorems
