/-
# KnuthSkilling Core - Stable Facade

This module provides a **stable re-export** of the core algebraic results.
It is designed to be a safe import target for downstream development
(including Shore-Johnson work) without coupling to internal implementation details.

## What's Exported

The "core algebra" layer:
- **Basic**: Ordered semigroup/monoid structures (`KSSemigroupBase`, `KnuthSkillingAlgebraBase`)
- **Algebra**: Iteration, separation axioms
- **Additive**: Appendix A - separation axioms + additive representation (⊕ → ℝ+)
- **Multiplicative**: Appendix B - product representation (⊗ → scaled multiplication)

## What's NOT Exported

- Shore-Johnson modules (depend on Core, not vice versa)
- Divergence/Entropy/Information theory (application layer)
- Probability calculus derivations (interpretation layer)
- Counterexamples (optional educational material)
- Explorations/research (unstable)

## Stability Guarantee

Files in this module are considered stable. Changes to their public API
should be coordinated with downstream users. Internal implementation
changes that preserve the API are allowed.

## Usage

```lean
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core

-- Access core structures
example : Type := KSSemigroupBase
example : Type := KnuthSkillingAlgebraBase
example : Type := KSSeparation
-- etc.
```
-/

-- Foundation layer
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Basic
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Algebra
import Mettapedia.ProbabilityTheory.KnuthSkilling.Core.Interfaces

-- Separation machinery (Alimov/Hölder path)
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Axioms

-- Main representation theorems
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative

-- Variational theorem (functional equation → log form)
import Mettapedia.ProbabilityTheory.KnuthSkilling.Variational.Main
