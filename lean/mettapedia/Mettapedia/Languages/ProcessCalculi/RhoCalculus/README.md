# ρ-Calculus

Lean 4.28 formalization of Meredith's ρ-calculus (Meredith & Radestock 2005).
**11 files, 4,954 lines. Zero sorry.**

Part of `papers/process-calculi.tex` (Section 2).

## Key Idea

Names *are* quoted processes: every name `x` has the form `@P` for some
process `P`. The key equation is `@(*(n)) = n`. This dissolves the
traditional name/process distinction and makes the calculus reflective.

## Syntax (locally nameless)

```
Pattern ::= pNil | pPar P Q | pInput x y P | pOutput x y | pDrop x | pQuote P
```

`pQuote`/`pDrop` implement the reflection. `pInput`/`pOutput` are the
communication primitives. Locally nameless representation throughout.

## Modules

| File | Contents |
|------|----------|
| `Types.lean` | `Pattern` type, quote/dereference, COMM reduction |
| `StructuralCongruence.lean` | Locally nameless SC; par-flatten, α-equiv, par-perm, par-comm |
| `Reduction.lean` | COMM rule with locally nameless substitution |
| `MultiStep.lean` | `ReducesStar`, `ReducesN` (n-step) |
| `Engine.lean` | Executable rewrite engine (COMM, DROP, PAR); proven sound |
| `Soundness.lean` | Type preservation under substitution |
| `Context.lean` | Evaluation contexts, labeled transitions |
| `DerivedRepNu.lean` | Derived replication and restriction |
| `SpiceRule.lean` | Spice calculus — n-step lookahead (Meredith 2026) |
| `CommRule.lean` | COMM with n-step lookahead |
| `PresentMoment.lean` | Present moment: surface + internal channels |

## Key Results

- Executable engine sound w.r.t. reduction relation
- Spice calculus recovers standard ρ-calculus at n = 0
- SC-quotiented Hennessy-Milner (assumption-free for finite-carrier canonical relations)
- ρ-calculus Galois connection *is* diamond-box duality for modal μ-calculus

## References

- Meredith, L.G. & Radestock, M. (2005). "A Reflective Higher-Order Calculus"
- Meredith, L.G. (2026). "How the Agents Got Their Present Moment" (Spice calculus)
