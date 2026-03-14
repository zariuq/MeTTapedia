# Conformance

Runtime/spec boundary testing: proving that **input → output**
derivations in Lean match the behaviour expected by unit tests and
runtime implementations. **6 files, ~2,700 lines. Zero sorry. No
`native_decide`.**

## Core Idea

A conformance proof takes a concrete input (space + query, or config +
pattern), runs it through both the formal spec and the runtime backend,
and proves the outputs are identical — typically by `rfl` on computable
definitions, or via kernel-checked `decide` on Bool fixtures bridged to
Prop theorems with `decide_eq_true_eq.mp`.

This closes the gap between "the spec says X" and "the implementation
returns X": if both sides reduce to the same normal form in Lean's
kernel, the runtime and spec agree by *definitional* equality. No
external test harness is needed — the kernel *is* the test runner.

## Modules

### `SimpleHE.lean` (322 lines, 9 fixtures + 6 theorem anchors)

Conformance between the `Simple` finite-state backend
(`Algorithms.MeTTa.Simple.Session`) and the formal HE interpreter spec
(`HE.Interpreter`). Tests cover:

- **Basic rewriting**: `f(a) = b` → query `f(a)` → `[b]`
- **Chained rewrites**: `g(a) → f(a) → b`
- **Non-determinism**: multiple rules for one LHS
- **No-reduction**: unknown expressions preserved
- **Pattern variables**: `f(x) = result(x)` with concrete substitution
- **Untyped identity**: `id(x) = x`
- **Duplicate rules**: same rule twice → duplicate outputs
- **Premise relations**: conditional rewrite gated by `allowed(alpha)`
- **Premise builtins**: conditional rewrite gated by `palette(warm)`

Translation layer: `atomToFrozen?` / `frozenToAtom` bridges `Atom`
(spec) ↔ `FrozenHEAtom` (runtime).

### `SimplePeTTa.lean` (1,070 lines, 48 checks + 11 theorems)

Cross-engine equivalence between the PeTTa runtime and the
`OSLF.MeTTaIL.Engine` reference evaluator. The most comprehensive
conformance module:

- **Bidirectional translation** (`Core` ↔ `Spec`) for all MeTTaIL types:
  patterns, equations, rules, language defs — with round-trip proofs
- **Basic evaluation** (3): simple, nested, non-determinism
- **Premise handling** (2): relation facts, builtin facts
- **Space matching** (13): pattern match against facts, multi-fact
  instantiation, shared-variable constraints, conjunction, named spaces
- **Session/state** (4): dynamic `add-atom`, `remove-atom`, nested
  side-effects
- **Intrinsic operations** (4): arithmetic (`+`, `-`, `*`, `%`),
  comparison (`<`), equality (`==`, `!=`)
- **Translation round-trips** (4): pattern, rule, language-def, tuple
- **Profile checksum drift** (5): detect semantic drift between engines

### `HEParserConformance.lean` (108 lines, 9 Bool checks)

Parser conformance for HE syntax profiles (compatibility vs canonical).
Tests that `!name` parses as symbol in compatibility mode but as
`!(eval (name))` in canonical mode; that `(= (f a) b)` → `defineEq`;
that `(: foo Bar)` → `defineType`; that bare `!` is rejected; etc.

### `PeTTaArtifactBridge.lean` (82 lines, 4 theorems)

Frozen `PeTTaConfig` round-trips through formal `PeTTaSpace`: facts and
rewrite rules map correctly both directions. Establishes the artifact
source-of-truth boundary between runtime lowering and formal
verification.

### `PeTTaBackendSpaceCompat.lean` (542 lines, 20+ theorems)

Proves `&mork` space references normalize to `&self` (the only currently
proved default atomspace). Covers normalization of match, get-atoms,
add-atom, remove-atom, collapse, let, chain, let\*, progn, prog1.
Proves normalized queries still satisfy `PeTTaEval`,
`PeTTaSpaceCoreQuery`, and `SpaceEffectFragment` predicates.

### `PeTTaCompatHeadBoundary.lean` (574 lines, 18+ theorems)

Two-phase compat-head lowering architecture:

1. **External witness phase**: grounded oracle evaluation (e.g.
   `is-member` tuple membership check) produces witnesses
2. **Residual MORK phase**: actual MORK source rules fire on the
   workspace using those witnesses

Proves binding-flow soundness: witness bindings instantiate the residual
body the same way MORK's substitution does.
`TupleMembershipOracleContract` grounds the external witness phase.
