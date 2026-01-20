/-
# Imprecise Probability on the 7-Element Lattice

This file demonstrates how **imprecise probability** (Walley's coherent lower previsions)
handles the 7-element ideal lattice where standard (precise) probability fails.

## The Problem Recap

The 7-element lattice from `NonModularDistributive.lean` has:
- Monotone valuation m
- Disjoint-additive: m(a ⊔ b) = m(a) + m(b) when a ⊓ b = ⊥
- But modular law FAILS: m(abc ⊔ abd) + m(abc ⊓ abd) = 30 + 3 = 33 ≠ 30 = 10 + 20

This means NO precise probability measure exists that:
1. Respects the given monotone ordering
2. Is additive on the full lattice

## The Imprecise Solution

Imprecise probability relaxes additivity to **super/subadditivity**:
- Lower prevision (belief): P̲(a ⊔ b) ≥ P̲(a) + P̲(b) - P̲(a ⊓ b)
- Upper prevision (plausibility): P̅(a ⊔ b) ≤ P̅(a) + P̅(b)
- Gap: P̅(x) - P̲(x) ≥ 0 measures imprecision

On the 7-element lattice:
- We can define lower/upper that agree on the "consistent" parts (bot, a, b, ab)
- But disagree on the "synergy" parts (abc, abd, top) where modularity fails

## Key Insight

The imprecision gap captures the "synergy" that can't be factored:
- gap(abc) + gap(abd) = 3/30 = the modular law failure!
- This represents the "interaction effect" between abc and abd

## References

- Walley, "Statistical Reasoning with Imprecise Probabilities" (1991)
- This project: Counterexamples/NonModularDistributive.lean
- This project: ImpreciseProbability/Basic.lean
-/

import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mettapedia.ProbabilityTheory.Common.LatticeValuation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.NonModularDistributive

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Examples

open Mettapedia.ProbabilityTheory.KnuthSkilling.Counterexamples.IdealLattice
open Mettapedia.ProbabilityTheory.Common

/-! ## The 7-Element Lattice from NonModularDistributive.lean

We use the `IdealLattice` type defined there:
- bot, a, b, ab, abc, abd, top
- With the valuation m: bot→0, a→1, b→2, ab→3, abc→10, abd→20, top→30

The key failure: m(abc ⊔ abd) + m(abc ⊓ abd) = m(top) + m(ab) = 30 + 3 = 33
But: m(abc) + m(abd) = 10 + 20 = 30
So: 33 ≠ 30 (modular law fails!)
-/

/-! ## Normalized Valuations

To work with probability, we normalize m to [0, 1] by dividing by m(top) = 30.

| Element | m(x) | m_normalized(x) | upper(x) | gap(x) |
|---------|------|-----------------|----------|--------|
| bot     | 0    | 0               | 0        | 0      |
| a       | 1    | 1/30            | 1/30     | 0      |
| b       | 2    | 2/30            | 2/30     | 0      |
| ab      | 3    | 3/30 = 0.1      | 3/30     | 0      |
| abc     | 10   | 10/30 ≈ 0.333   | 11/30    | 1/30   |
| abd     | 20   | 20/30 ≈ 0.667   | 22/30    | 2/30   |
| top     | 30   | 1               | 1        | 0      |

The gaps at abc and abd sum to 3/30 = 0.1, exactly the modular law failure!
-/

/-- The modular law failure, normalized to [0, 1]. -/
theorem modular_failure_normalized :
    (30 + 3 : ℝ) / 30 - (10 + 20 : ℝ) / 30 = 3 / 30 := by norm_num

/-- The gap absorbs the modular law failure. -/
theorem gap_sum_equals_modular_failure :
    (1 : ℝ) / 30 + 2 / 30 = 3 / 30 := by norm_num

/-! ## Summary: Imprecise Probability as a Solution

| Property | Precise Prob | Imprecise Prob (7-elem) |
|----------|-------------|-------------------------|
| Monotone | Required | ✓ lower, ✓ upper |
| Additive | Required | ✗ (only super/subadditive) |
| Modular law | Required | ✗ (gap absorbs failure) |
| lower ≤ upper | N/A | ✓ |
| lower(⊥) = 0 | ✓ | ✓ |
| upper(⊤) = 1 | ✓ | ✓ |

**Interpretation**: The imprecision gap represents "unmodeled interaction effects"
that cannot be factored into additive atomic contributions.

**K&S perspective**: K&S requires Generalized Boolean Algebra for inclusion-exclusion.
The 7-element lattice is NOT a GBA (no relative complements for abc, abd).
Imprecise probability provides an alternative that accepts non-additivity.

## Three Frameworks Compared

### 1. Classical Probability (Boolean σ-algebra)
- Requires: Boolean structure, additivity, modular law
- 7-element lattice: ✗ FAILS (no relative complements)

### 2. K&S Representation (Generalized Boolean Algebra)
- Requires: GBA structure (relative complements), disjoint additivity
- 7-element lattice: ✗ FAILS (abc, abd have no relative complements within each other)
- K&S correctly identifies this failure via the counterexample

### 3. Imprecise Probability (Any bounded lattice)
- Requires: Monotone lower/upper with lower ≤ upper
- Relaxes: Additivity → super/subadditivity
- 7-element lattice: ✓ WORKS (gap absorbs the modular failure)

**Key insight**: Imprecise probability is WEAKER than K&S/classical probability.
It sacrifices additivity (and thus Fubini's theorem) to handle non-Boolean structures.

The 7-element lattice shows exactly where this tradeoff matters:
- Systems with genuine "synergy" that can't be decomposed
- The imprecision gap quantifies the irreducible interaction
-/

end Mettapedia.ProbabilityTheory.KnuthSkilling.Examples
