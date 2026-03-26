# MeTTailCore

Lean 4 formalization of MeTTa surface syntax specs and intermediate language
(MeTTaIL) runtime semantics.

**Toolchain:** Lean 4.28.0

```bash
cd lean-projects/batteries/mettail-core
lake build
```

## Two Layers

### MeTTaSyntax — surface parsing and round-trip

- `Spec.lean` — lexer, eval-prefix, lowering policies, command dispatch specs
- `Roundtrip.lean` — S-expression encode/decode parameterized by `AtomEncodingSpec`; zero-sorry round-trip proof (`decode (encode x) = some x`)
- `Pretty.lean` — pattern rendering to human-readable syntax
- `CommandIR.lean` — normalized command IR (eval, facts, definitions, imports, space ops)

### MeTTaIL — core runtime semantics

- `Syntax.lean` — type expressions, collection types, core data model
- `Match.lean` — pattern matching, bindings, tuple views, multi-element selection
- `Substitution.lean` — variable substitution via `SubstEnv`, bound variable opening
- `Engine.lean` — rewrite step semantics, congruence reductions, one-level reduction
- `RewriteIR.lean` — rewrite rules with mode (ordinaryForward, compatHead, symbolicOutput), premises, var flow
- `TransitionSpec.lean` — transition contracts (deterministicReduction, memoizationSafe, etc.)
- `LookupPlan.lean` — demand signatures, usage kinds (enumerate, exists, negatedExists), binding modes
- `Profile.lean` — builtin relation tables, runtime policy, `SpecBundle`
- `EffectSafety.lean` — effect lattice (pureStructural < readOnlyLookup < ... < oracleIO), memoization shapes

## Key Properties

- **Round-trip correctness** — kernel-checked, zero sorry
- **Effect composition** — conservative join over ordered effect lattice
- **Demand-driven lookup** — optimize via usage patterns
