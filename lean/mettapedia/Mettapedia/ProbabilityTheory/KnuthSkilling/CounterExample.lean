/-
# Counter-Examples for Knuth-Skilling Formalization

This file contains examples showing limitations of specific proof strategies:

1. **L = M witness strategy failure** (ℝ with addition):
   PROVEN - A specific witness construction for separation fails when L=M

2. **Non-commutativity breaking scaling** (free monoid):
   DOCUMENTED - The algebraic identity μ(F, n·r) = (μ(F, r))^n requires
   commutativity. The actual proof is in CounterExamples.lean.
-/

import Mathlib.Data.Real.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA

namespace Mettapedia.ProbabilityTheory.KnuthSkilling

/-! ## The Counter-Example

Let the algebra be ℝ with op = + and ident = 0.
Choose:
- a = 10
- x = 3.5  
- y = 3.6

Then:
- x < y ✓
- N = 1 (minimal with x < a^1) ✓
- M = 3 (minimal with a ≤ x^M = 3x) ✓
- L = 3 (minimal with a < y^L = 3y) ✓
- So L = M = 3 ✓

The witness strategy proposes:
- m = L + (M-1) = 5
- n' = 1 (maximal with n'·a ≤ (M-1)x + a = 17)
- n = n'+1 = 2

Separation condition: x^m < a^n ≤ y^m
- Lower: 5x < 2a ⟺ 17.5 < 20 ✓
- Upper: 2a ≤ 5y ⟺ 20 ≤ 18 ✗

Therefore, the witness construction FAILS.
-/

/-- The counter-example proving witness (n'+1, L+(M-1)) fails when L = M.

This theorem shows that for specific values a=10, x=3.5, y=3.6 with M=L=3,
the proposed witness (n=2, m=5) fails the upper bound.

The key point: x < y < a, with M=3 minimal s.t. 3x ≥ a, and L=3 minimal s.t. 3y > a.
The witness m = L + (M-1) = 5 and n = 2 fails because 2·a = 20 > 18 = 5·y. -/
theorem counterexample_L_eq_M_witness_fails :
  ∃ (a x y : ℝ),
    -- Basic ordering
    0 < a ∧ 0 < x ∧ 0 < y ∧ x < y ∧
    -- x < a (so N=1 works)
    x < a ∧
    -- M = 3 is minimal with a ≤ M·x
    (∀ k : ℕ, k > 0 → k < 3 → (k : ℝ) * x < a) ∧
    3 * x ≥ a ∧
    -- L = 3 is minimal with a < L·y
    (∀ k : ℕ, k > 0 → k < 3 → (k : ℝ) * y ≤ a) ∧
    3 * y > a ∧
    -- The witness strategy (n=2, m=5) FAILS the upper bound
    let M : ℕ := 3
    let L : ℕ := 3
    let m := L + (M - 1)  -- 5
    let n' := 1           -- floor((2x + a)/a)
    let n := n' + 1       -- 2
    ¬ ((n : ℝ) * a ≤ (m : ℝ) * y) := by
  -- Use a = 10, x = 3.5, y = 3.6
  refine ⟨10, 3.5, 3.6, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    ?hM_min, by norm_num, ?hL_min, by norm_num, by norm_num⟩
  · -- M = 3 is minimal: k·3.5 < 10 for k ∈ {1, 2}
    intro k hk_pos hk_lt
    interval_cases k <;> norm_num
  · -- L = 3 is minimal: k·3.6 ≤ 10 for k ∈ {1, 2}
    intro k hk_pos hk_lt
    interval_cases k <;> norm_num

/-- Simplified version showing just the key inequality failure -/
theorem counterexample_simplified :
  let a : ℝ := 10
  let y : ℝ := 3.6
  let n : ℕ := 2
  let m : ℕ := 5
  -- The upper bound requires: a^n ≤ y^m, i.e., 20 ≤ 18, which is FALSE
  ¬ ((n : ℝ) * a ≤ (m : ℝ) * y) := by
  simp only []
  norm_num

/-- The lower bound DOES work with these witnesses -/
theorem counterexample_lower_bound_works :
  let a : ℝ := 10
  let x : ℝ := 3.5
  let m : ℕ := 5
  let n : ℕ := 2
  -- 5·3.5 = 17.5 < 20 = 2·10 ✓
  (m : ℝ) * x < (n : ℝ) * a := by
  simp only []
  norm_num

/-- The upper bound fails because 5·y < 2·a (18 < 20) -/
theorem counterexample_upper_bound_inequality :
  let a : ℝ := 10
  let y : ℝ := 3.6
  let m : ℕ := 5
  let n : ℕ := 2
  -- 5·3.6 = 18 < 20 = 2·10
  -- This is the OPPOSITE of what we need (a^n ≤ y^m)
  (m : ℝ) * y < (n : ℝ) * a := by
  simp only []
  norm_num

/-! ## Mathematical Insight

**What this counterexample shows**: A specific witness construction strategy FAILS for L=M.

The failure occurs because when L = M, we have:
- a ≤ x^M (x has "grown large enough")
- m = 2M - 1 (proposed witness multiplicity)
- x^m = x^{M-1} ⊕ x^M ≥ x^{M-1} ⊕ a

The crossing point n' is chosen so that:
- a^{n'} ≤ x^{M-1} ⊕ a < a^{n'+1}

But when we compute x^m:
- x^m = x^{M-1} ⊕ x^M
- Since x^M ≥ a, we have x^m ≥ x^{M-1} ⊕ a

This means a^{n'+1} might fall in the gap (x^{M-1} ⊕ a, x^m],
breaking the lower bound x^m < a^{n'+1}.

Even when the lower bound works (as in our a=10, x=3.5, y=3.6 example),
the upper bound a^{n'+1} ≤ y^m can fail because n'+1 is calibrated
for the gap at x^{M-1}, not at the larger x^m.

**What this does NOT show**: That separation witnesses don't exist in general.
Other witness constructions may succeed. This merely shows one strategy fails.
-/

/-! ## Counter-Example: Non-Commutativity Breaks Scaling

**Key Insight** (per GPT-5.1 Pro § 4.1): The equality μ(F, n·r) = (μ(F, r))^n
is **FALSE in GENERAL** for multi-type families without commutativity.

**Informal Counterexample**:
Consider a non-commutative KnuthSkillingAlgebra with two atom types a, b where a⊕b ≠ b⊕a.

For family F with atoms {a, b} and multiplicity vector r = (1, 1):
- μ(F, (1,1)) = a ⊕ b
- μ(F, 2·(1,1)) = μ(F, (2,2)) = a² ⊕ b²
- (μ(F, (1,1)))² = (a ⊕ b) ⊕ (a ⊕ b)

**The inequality**: a² ⊕ b² ≠ (a ⊕ b)² in general without commutativity!

Expansion of (a ⊕ b)²:
  (a ⊕ b) ⊕ (a ⊕ b)
  = a ⊕ (b ⊕ a) ⊕ b    (by associativity)
  = a ⊕ (a ⊕ b) ⊕ b    (if commutativity holds: b⊕a = a⊕b)
  = (a ⊕ a) ⊕ (b ⊕ b)  (by associativity + commutativity)
  = a² ⊕ b²

**Without commutativity**, the step b⊕a = a⊕b fails, so:
  (a ⊕ b) ⊕ (a ⊕ b) = a ⊕ (b ⊕ a) ⊕ b ≠ a² ⊕ b²

**Concrete model**: Consider the free monoid on {a, b} with concatenation as ⊕.
Then (a ⊕ b) ⊕ (a ⊕ b) = "abab" while a² ⊕ b² = "aabb", clearly different!

This proves that commutativity is NECESSARY for μ(F, n·r) = (μ(F, r))^n.
-/

section NonCommutativityCounterExample

open KnuthSkillingAlgebra AppendixA

variable {α : Type*} [KnuthSkillingAlgebra α]

/-! ### Mathematical Observations

**What IS proven** (in CounterExamples.lean):
- `free_monoid_counterexample`: In the free monoid, (a⊕b)² ≠ a²⊕b²

**What this demonstrates**:
- The algebraic identity μ(F, n·r) = (μ(F, r))^n requires commutativity
- Without commutativity: (a⊕b)² = a⊕b⊕a⊕b (interleaved) ≠ a²⊕b² (grouped)
- The K&S axioms do NOT include commutativity

**What remains to be shown** (not yet formalized):
- A full `KnuthSkillingAlgebra` instance for the free monoid with shortlex order
- Once constructed, this would provide a formal model where μ-scaling fails

### Mathematical Moral

The scaling equality μ(F, n·r) = (μ(F, r))^n requires one of:
1. **Commutativity** (sufficient; standard algebra)
2. **B-case restriction**: μ(F, r) = d^u for external d (uses order/Θ structure)

The K&S Appendix A cleverly uses approach (2) to derive commutativity as a THEOREM,
not an axiom. This is the deep insight: commutativity emerges from the representation!
-/

end NonCommutativityCounterExample

end Mettapedia.ProbabilityTheory.KnuthSkilling
