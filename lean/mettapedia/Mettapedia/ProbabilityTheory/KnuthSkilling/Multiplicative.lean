import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.FunctionalEquation
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.DirectProduct
-- Common interface for Appendix B results (both paths provide this)
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.ScaledMultRep
-- K&S's actual path (Appendix A → Appendix B)
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Main
-- Alternative path (direct derivation, bypasses Appendix A)
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.Proofs.Direct.DirectProof
import Mettapedia.ProbabilityTheory.KnuthSkilling.Multiplicative.StrictMonoSolution

/-!
This module is the public entry point for the Knuth–Skilling (Appendix B) *product theorem*.

## Two Derivation Paths

This formalization provides **two complete paths** to the product rule:

### Path 1: K&S's Actual Derivation (Recommended)
- `...Multiplicative.Main`: Uses `AdditiveOrderIsoRep` (from Appendix A) to derive the product
  equation, then solves it to show `⊗` is multiplication up to scale.
- This follows K&S's paper exactly: "apply Appendix A again to `⊗`".

### Path 2: Alternative (Aczél's Direct Approach)
- `...Multiplicative/Proofs/Direct/DirectProof.lean`: Bypasses Appendix A entirely by deriving scaled
  multiplication directly from distributivity + associativity.
- Useful because Appendix A requires identity = minimum, which fails for `(0,∞)`.

Both paths arrive at the same conclusion: `x ⊗ y = (x * y) / C`.

## Common Interface: ScaledMultRep

Both paths provide the **`ScaledMultRep`** interface, which captures the Appendix B result:
- `ScaledMultRep.C`: The scale constant C > 0
- `ScaledMultRep.tensor_eq`: tensor x y = (x * y) / C

Downstream code (ConditionalProbability, ProbabilityDerivation, etc.) should depend on
`ScaledMultRep`, NOT on specific proof paths. This design parallels `AdditiveOrderIsoRep`
for Appendix A.

## File Organization

- `...Multiplicative.ScaledMultRep`: **Common interface** - `ScaledMultRep` structure (tensor = scaled mult)
- `...Multiplicative.FunctionalEquation`: complete solver for the product equation
- `...Multiplicative.Basic`: derives the product equation from Axioms 3–4 + `AdditiveOrderIsoRep`
- `...Multiplicative.Main`: **K&S path** - combines bridge + solver, provides `ScaledMultRep`
- `...Multiplicative/Proofs/Direct/DirectProof.lean`: **Alternative path** - direct derivation, provides `ScaledMultRep`
- `...Multiplicative.StrictMonoSolution`: derives continuity from `ProductEquation + StrictMono`
- `...Multiplicative.FibonacciProof`: **optional/historical** (not imported, heavy dependencies)
- `...Multiplicative.DirectProduct`: lattice-level bookkeeping for event product `×`

## WARNING: Circular Reasoning Anti-Pattern

 A previous file `EventBridge.lean` was DELETED because it contained circular reasoning:
  it defined `mulTensor := multiplication` and then "proved" multiplication equals
  scaled multiplication. This proves nothing!

**DO NOT** try to "bridge" event-level to scalar-level by defining:
```
abbrev mulTensor := mulPos  -- WRONG: assumes tensor IS multiplication
```

The correct approach is:
1. Start with an ABSTRACT tensor ⊗ satisfying Axioms 3-4
2. Use `DirectProof.lean` to conclude ⊗ = scaled multiplication
3. Do NOT define ⊗ := multiplication and then "verify" properties
-/
