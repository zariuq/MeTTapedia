/-
# KnuthSkilling Scale - Ordered Algebraic Structures

This module provides the **official interface** for the ordered scale structures
used throughout the KnuthSkilling formalization.

## Hierarchy

The scale structures form a refinement hierarchy:

1. **`KSSemigroupBase`** (identity-free)
   - Linearly ordered
   - Associative operation `op`
   - Strict monotonicity in both arguments
   - *This is the Alimov/Hölder classical setting*

2. **`KnuthSkillingAlgebraBase`** (with identity)
   - Adds: identity element `ident`
   - Adds: `ident` is minimum (`ident_le`)
   - *This is the probability/valuation setting*

3. **`KSSeparation`** / **`KSSeparationSemigroup`**
   - Density axiom: no infinitesimal gaps
   - Equivalent to "No Anomalous Pairs" (Alimov)
   - *Ensures embedding into ℝ*

## Key Results

From these structures we derive:
- **Commutativity** (from separation - not assumed!)
- **Archimedean property** (from separation)
- **Embedding into ℝ** (Hölder's theorem)

## Usage

```lean
import Mettapedia.ProbabilityTheory.KnuthSkilling.Scale

variable {α : Type*} [KSSemigroupBase α]

-- Identity-free ordered semigroup operations available
example (x y : α) : op x y = op y x := by
  -- requires KSSeparationSemigroup for commutativity
  sorry
```
-/

-- Core structures
import Mettapedia.ProbabilityTheory.KnuthSkilling.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Algebra

-- Separation axioms and consequences
import Mettapedia.ProbabilityTheory.KnuthSkilling.Separation
