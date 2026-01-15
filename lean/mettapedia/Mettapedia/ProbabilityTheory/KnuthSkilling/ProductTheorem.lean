import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FunctionalEquation
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.DirectProduct
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.Main
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.AczelTheorem
import Mettapedia.ProbabilityTheory.KnuthSkilling.ProductTheorem.FibonacciProof

/-!
This module is the public entry point for the Knuth–Skilling (Appendix B) *product theorem*.

The development is split as follows:

- `...ProductTheorem.FunctionalEquation`: a sorry-free solver for the product equation
  (K&S Appendix B), yielding exponential solutions under explicit regularity assumptions.
- `...ProductTheorem.Basic`: derives the product equation from the scalar axioms for `⊗`
  in the \"Independence\" section (Axioms 3–4) together with an additive order-isomorphism
  representation `Θ(x ⊗ t) = Θ x + Θ t`.
- `...ProductTheorem.Main`: combines the bridge and the solver to conclude that `⊗` is
  multiplication up to a global scale constant.
- `...ProductTheorem.AczelTheorem`: an alternative Lean-friendly route that avoids assuming
  an Aczél-style representation theorem for `⊗` on `(0,∞)`, deriving scaled multiplication
  directly from distributivity, associativity, and regularity.
- `...ProductTheorem.FibonacciProof`: **K&S's actual proof** from Appendix B lines 1982-2082,
  using Fibonacci recurrence and golden ratio density (WIP, has sorries).
- `...ProductTheorem.DirectProduct`: lattice-level bookkeeping for the event product `×`
  used in the "Independence" subsection, with the canonical `Set` model.

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
2. Use `AczelTheorem.lean` to conclude ⊗ = scaled multiplication
3. Do NOT define ⊗ := multiplication and then "verify" properties
-/
