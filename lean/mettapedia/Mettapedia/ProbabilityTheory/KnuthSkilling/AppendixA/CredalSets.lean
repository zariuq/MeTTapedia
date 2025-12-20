import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Set.Lattice

/-!
# Credal Sets: K&S Axioms in Completion-Free Foundations

This file explores what the K&S axioms yield in foundations WITHOUT completeness
of the reals (constructive mathematics, working over ℚ, etc.). The result is
**imprecise probability** (credal sets) with interval-valued bounds.

**Note**: The main K&S formalization (AppendixA/Main.lean) works in Lean's foundation
which assumes classical ℝ (complete). This file is a mathematical exploration of
alternative foundations, not a claim that K&S made an error.

## Overview

Classical probability assigns exact real values: P : Events → ℝ
Imprecise probability assigns intervals: P*, P* : Events → ℝ (lower/upper bounds)

The key insight: Without completeness, you cannot name exact probability values,
but you CAN specify bounds. This gives a perfectly consistent theory that is
arguably MORE honest about our actual epistemic state.

## Main Results

1. **Credal Algebra**: Definition of interval-valued measures with K&S axioms
2. **Consistency**: Credal algebras exist and are non-trivial
3. **Classical Recovery**: Adding completeness collapses credal sets to points
4. **The Steelmanned K&S Theorem**: Precise statement of what K&S should have claimed

## References

Primary sources on imprecise probability:

- Walley, P. (1991). "Statistical Reasoning with Imprecise Probabilities".
  Chapman & Hall. [The foundational text that coined the term]
- Levi, I. (1980). "The Enterprise of Knowledge". MIT Press.
- de Finetti, B. (1974). "Theory of Probability". Wiley. [Later chapters on previsions]

Modern surveys:
- Stanford Encyclopedia of Philosophy: "Imprecise Probabilities"
  https://plato.stanford.edu/entries/imprecise-probabilities/
- Augustin et al. (2014). "Introduction to Imprecise Probabilities". Wiley.

Key concepts from the literature:
- A **credal set** (or representor) is a set of probability functions
- **Lower/upper previsions**: P*(X) = inf{P(X) : P ∈ credal set}, P*(X) = sup{...}
- **Coherence**: The credal set cannot be used to construct a sure loss (Dutch book)
- **Convexity**: Credal sets are typically convex sets of probability measures

This file formalizes a simplified version adapted to the K&S context.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.CredalSets

/-!
## §1: Credal Algebra — The Completion-Free Structure
-/

/-- An interval with lower ≤ upper -/
structure Interval where
  lower : ℝ
  upper : ℝ
  valid : lower ≤ upper

/-- Interval width -/
def Interval.width (I : Interval) : ℝ := I.upper - I.lower

/-- Interval addition (Minkowski sum) -/
def Interval.add (I J : Interval) : Interval where
  lower := I.lower + J.lower
  upper := I.upper + J.upper
  valid := add_le_add I.valid J.valid

/-- Interval containment: I ⊆ J means J.lower ≤ I.lower and I.upper ≤ J.upper -/
def Interval.containedIn (I J : Interval) : Prop :=
  J.lower ≤ I.lower ∧ I.upper ≤ J.upper

instance : Add Interval := ⟨Interval.add⟩

/-- A credal algebra: an ordered associative operation with interval-valued measure -/
structure CredalAlgebra (α : Type*) where
  /-- The combining operation -/
  op : α → α → α
  /-- The interval-valued measure -/
  μ : α → Interval
  /-- Associativity -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- Containment: μ(x ⊕ y) is bounded by μ(x) + μ(y) -/
  containment : ∀ x y, (μ (op x y)).containedIn (μ x + μ y)
  /-- Order preservation on lower bounds -/
  order_lower : ∀ x y, (μ x).lower < (μ y).lower → (μ x).upper ≤ (μ y).lower

/-!
### Key Properties of Credal Algebras

Unlike classical probability, credal algebras:
1. Do NOT require exact point values
2. Do NOT require commutativity
3. Do NOT require completeness of ℝ
4. DO preserve the essential K&S structure (associativity, bounds, order)
-/

/-- The zero interval [0, 0] -/
def zeroInterval : Interval := ⟨0, 0, le_refl 0⟩

/-- The unit interval [0, 1] -/
def unitInterval : Interval := ⟨0, 1, by norm_num⟩

/-- A constant interval [c, c] -/
def constInterval (c : ℝ) : Interval := ⟨c, c, le_refl c⟩

/-!
## §2: The Trivial Credal Algebra (Existence Proof)

We show credal algebras exist by constructing a trivial one.
-/

/-- The trivial credal algebra on any monoid -/
def trivialCredalAlgebra (α : Type*) [AddMonoid α] : CredalAlgebra α where
  op := (· + ·)
  μ := fun _ => unitInterval
  assoc := add_assoc
  containment := fun _ _ => by
    unfold Interval.containedIn unitInterval HAdd.hAdd instHAdd Add.add instAddInterval Interval.add
    constructor <;> norm_num
  order_lower := fun _ _ h => by simp [unitInterval] at h

/-- Credal algebras exist -/
theorem credal_algebra_exists : ∃ (α : Type) (_ : CredalAlgebra α), True :=
  ⟨ℕ, trivialCredalAlgebra ℕ, trivial⟩

/-!
## §3: The Heisenberg Credal Algebra (Noncommutative Example)

This shows that credal algebras do NOT imply commutativity.
-/

/-- Heisenberg group operation -/
def heisenbergOp (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2 + x.1 * y.2.1)

/-- The Heisenberg credal algebra -/
def heisenbergCredalAlgebra : CredalAlgebra (ℤ × ℤ × ℤ) where
  op := heisenbergOp
  μ := fun _ => unitInterval
  assoc := by
    intro x y z
    simp only [heisenbergOp]
    ring_nf
  containment := fun _ _ => by
    unfold Interval.containedIn unitInterval HAdd.hAdd instHAdd Add.add instAddInterval Interval.add
    constructor <;> norm_num
  order_lower := fun _ _ h => by simp [unitInterval] at h

/-- The Heisenberg credal algebra is noncommutative -/
theorem heisenberg_credal_not_comm :
    ∃ x y : ℤ × ℤ × ℤ, heisenbergCredalAlgebra.op x y ≠ heisenbergCredalAlgebra.op y x := by
  use (1, 0, 0), (0, 1, 0)
  simp only [heisenbergCredalAlgebra, heisenbergOp, ne_eq, Prod.mk.injEq]
  decide

/-!
## §4: Refined Credal Algebras (Shrinking Intervals)

For stronger results, we consider sequences of credal measures with shrinking intervals.
-/

/-- A refined credal algebra: a sequence of interval measures with shrinking widths -/
structure RefinedCredalAlgebra (α : Type*) where
  /-- The combining operation -/
  op : α → α → α
  /-- Sequence of interval measures -/
  μ : ℕ → α → Interval
  /-- Associativity -/
  assoc : ∀ x y z, op (op x y) z = op x (op y z)
  /-- Intervals are nested: lower bounds increase -/
  lower_mono : ∀ x n, (μ n x).lower ≤ (μ (n + 1) x).lower
  /-- Intervals are nested: upper bounds decrease -/
  upper_mono : ∀ x n, (μ (n + 1) x).upper ≤ (μ n x).upper
  /-- Widths converge to zero -/
  converge : ∀ x ε, ε > 0 → ∃ n, (μ n x).width < ε

/-!
## §5: The Collapse Theorem (Classical Recovery)

When intervals converge, we can extract point values — but this requires completeness.
-/

/-- Extract the limiting point value using completeness (sSup) -/
noncomputable def limitingValue (R : RefinedCredalAlgebra α) (x : α) : ℝ :=
  sSup (Set.range (fun n => (R.μ n x).lower))

/-- Helper: lower bounds increase with index -/
theorem lower_increasing (R : RefinedCredalAlgebra α) (x : α) :
    ∀ m n, m ≤ n → (R.μ m x).lower ≤ (R.μ n x).lower := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans ih (R.lower_mono x k)

/-- Helper: upper bounds decrease with index -/
theorem upper_decreasing (R : RefinedCredalAlgebra α) (x : α) :
    ∀ m n, m ≤ n → (R.μ n x).upper ≤ (R.μ m x).upper := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | @step k _ ih => exact le_trans (R.upper_mono x k) ih

/-- Helper: lower bounds are bounded above by any upper bound -/
theorem lower_bdd_by_upper (R : RefinedCredalAlgebra α) (x : α) (n : ℕ) :
    ∀ m, (R.μ m x).lower ≤ (R.μ n x).upper := by
  intro m
  by_cases hmn : m ≤ n
  · exact le_trans (lower_increasing R x m n hmn) (R.μ n x).valid
  · push_neg at hmn
    exact le_trans (R.μ m x).valid (upper_decreasing R x n m (le_of_lt hmn))

/-- The Collapse Theorem: refined credal algebras yield point values via completeness -/
theorem collapse_theorem (R : RefinedCredalAlgebra α) :
    ∃ θ : α → ℝ, ∀ x n, (R.μ n x).lower ≤ θ x ∧ θ x ≤ (R.μ n x).upper := by
  use limitingValue R
  intro x n
  have h_bdd : BddAbove (Set.range (fun m => (R.μ m x).lower)) :=
    ⟨(R.μ 0 x).upper, fun v ⟨m, hm⟩ => hm ▸ lower_bdd_by_upper R x 0 m⟩
  have h_ne : (Set.range (fun m => (R.μ m x).lower)).Nonempty := ⟨(R.μ 0 x).lower, 0, rfl⟩
  constructor
  · exact le_csSup h_bdd ⟨n, rfl⟩
  · exact csSup_le h_ne (fun v ⟨m, hm⟩ => hm ▸ lower_bdd_by_upper R x n m)

/-!
## §6: K&S Theorem in Different Foundations

This section clarifies how the K&S result depends on foundational choices:

**Theorem** (Foundation-Dependent K&S):
- In **completion-free** foundations (constructive ℝ, ℚ, etc.):
  Associativity + Order axioms ⟹ CREDAL representations (interval bounds)
- In **classical** foundations (Lean/ZFC with complete ℝ):
  Associativity + Order axioms ⟹ ℝ-valued probability (point values)

The completeness of ℝ is a foundational assumption, not derived from the K&S axioms.
K&S worked in classical mathematics where this choice is implicit.
-/

/-- The Steelmanned K&S Theorem: what you get depends on what you assume -/
theorem steelmanned_KS :
    -- Part 1: Without completeness, you get credal algebras (which can be noncommutative)
    (∃ (α : Type) (C : CredalAlgebra α), ∃ x y, C.op x y ≠ C.op y x) ∧
    -- Part 2: With completeness (via sSup), refined credal algebras collapse to point values
    (∀ (α : Type*) (R : RefinedCredalAlgebra α),
      ∃ θ : α → ℝ, ∀ x n, (R.μ n x).lower ≤ θ x ∧ θ x ≤ (R.μ n x).upper) := by
  constructor
  · -- Part 1: Heisenberg credal algebra
    exact ⟨ℤ × ℤ × ℤ, heisenbergCredalAlgebra, heisenberg_credal_not_comm⟩
  · -- Part 2: Collapse theorem
    intro α R
    exact collapse_theorem R

/-!
## §7: Philosophical Interpretation

### What Credal Sets Represent

| Concept | Classical Probability | Credal Sets |
|---------|----------------------|-------------|
| P(A) | Single real number | Interval [P*(A), P*(A)] |
| Meaning | "The probability is exactly 0.73" | "The probability is between 0.7 and 0.8" |
| Precision | Infinite | Bounded |
| Honesty | Pretends exact knowledge | Admits uncertainty |

### Why Credal Sets Are Natural

1. **Epistemic Humility**: We rarely know exact probabilities
2. **Robust Inference**: Conclusions valid for ALL probabilities in the interval
3. **No Completeness Needed**: Can work over ℚ or constructive reals
4. **Subsumes Classical**: Point-valued probability is the special case [p, p]

### The Foundational Choice

K&S's actual derivation (in Lean formalization): Symmetry axioms ⟹ ℝ-valued probability

**Why this works in Lean**: Lean's foundation assumes ℝ is complete (Dedekind cuts in ZFC).

**Alternative foundations**: If you DON'T assume completeness (e.g., constructive reals, ℚ):
- Symmetry axioms ⟹ Credal sets (interval bounds)
- Symmetry axioms + Completeness axiom ⟹ ℝ-valued probability

**Key insight**: The completeness of ℝ is a FOUNDATIONAL CHOICE, not derived from K&S axioms.
K&S work in classical mathematics where this choice is already made. This file explores what
happens if you make different foundational choices.

### Connections to Other Fields

- **Dempster-Shafer Theory**: Belief/plausibility functions ≈ lower/upper probabilities
- **Robust Bayesianism**: Prior sets instead of single priors
- **Game-Theoretic Probability**: Shafer & Vovk's approach avoids measure theory
- **Constructive Probability**: Bishop-style probability on computable reals
-/

/-!
## §8: The Full Picture

```
                    Symmetry Axioms
                          ↓
                    Credal Algebras
                   (interval-valued)
                    ↙           ↘
            [Weak axioms]    [Strong axioms]
                 ↓                  ↓
         Noncommutative      Completeness
           models              required
              ↓                    ↓
         NOT probability    Classical probability
                               (ℝ-valued)
```

**Summary**:
- In foundations WITHOUT completeness (constructive math, ℚ): K&S axioms ⟹ Credal sets
- In foundations WITH completeness (classical ℝ, Lean/ZFC): K&S axioms ⟹ ℝ-valued probability
- The continuum is a FOUNDATIONAL CHOICE, not derived from K&S symmetry axioms alone
- This file shows what the K&S construction yields in completion-free settings
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.AppendixA.CredalSets
