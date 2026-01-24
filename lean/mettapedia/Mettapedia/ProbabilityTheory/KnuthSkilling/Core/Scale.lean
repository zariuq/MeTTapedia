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

2. **`KnuthSkillingMonoidBase`** (identity, no bottom assumption)
   - Adds: identity element `ident` with left/right identity laws
   - *Useful for normalization Θ(ident)=0 without assuming `ident_le`*

3. **`KnuthSkillingAlgebraBase`** (probability/valuation setting)
   - Adds: `ident` is minimum (`ident_le`)
   - *This is the setting where every element is “nonnegative” (≥ ident)*

4. **`KSSeparation`** / **`KSSeparationSemigroup`**
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
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Scale

variable {α : Type*} [KSSemigroupBase α]

-- Identity-free ordered semigroup operations available
-- (To prove commutativity, add a separation/representation hypothesis; omitted here.)
```
-/

-- Core structures
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra

-- Separation axioms and consequences
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms
